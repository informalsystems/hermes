use alloc::sync::Arc;
use core::str::FromStr;
use std::thread;

use core::time::Duration;

use ibc_proto::ibc::applications::fee::v1::{
    QueryIncentivizedPacketRequest, QueryIncentivizedPacketResponse,
};
use ibc_proto::Protobuf;
use ibc_relayer_types::applications::ics31_icq::response::CrossChainQueryResponse;
use ibc_relayer_types::clients::ics07_tendermint::client_state::{
    AllowUpdate, ClientState as TmClientState,
};
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TmHeader;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::core::ics24_host::path::{
    AcksPath, ChannelEndsPath, ClientConsensusStatePath, ClientStatePath, CommitmentsPath,
    ConnectionsPath, ReceiptsPath, SeqRecvsPath,
};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height as ICSHeight;
use namada_ibc::storage;
use namada_parameters::{storage as param_storage, EpochDuration};
use namada_sdk::address::{Address, InternalAddress};
use namada_sdk::borsh::BorshDeserialize;
use namada_sdk::io::NullIo;
use namada_sdk::masp::fs::FsShieldedUtils;
use namada_sdk::masp::DefaultLogger;
use namada_sdk::proof_of_stake::storage_key as pos_storage_key;
use namada_sdk::proof_of_stake::OwnedPosParams;
use namada_sdk::queries::Client as SdkClient;
use namada_sdk::state::ics23_specs::ibc_proof_specs;
use namada_sdk::state::Sha256Hasher;
use namada_sdk::storage::{Key, KeySeg, PrefixValue};
use namada_sdk::wallet::Store;
use namada_sdk::wallet::Wallet;
use namada_sdk::{rpc, Namada, NamadaImpl};
use namada_trans_token::storage_key::{balance_key, denom_key, is_any_token_balance_key};
use namada_trans_token::{Amount, DenominatedAmount, Denomination};
use tendermint::block::Height as TmHeight;
use tendermint::{node, Time};
use tendermint_light_client::types::LightBlock as TMLightBlock;
use tendermint_rpc::client::CompatMode;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{Client, HttpClient};
use tokio::runtime::Runtime as TokioRuntime;

use crate::account::Balance;
use crate::chain::client::ClientSettings;
use crate::chain::cosmos::config::CosmosSdkConfig;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::cosmos::version::Specs;
use crate::chain::endpoint::{ChainEndpoint, ChainStatus, HealthCheck};
use crate::chain::handle::Subscription;
use crate::chain::requests::*;
use crate::chain::tracking::TrackedMsgs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::error::Error as ConfigError;
use crate::config::ChainConfig;
use crate::consensus_state::AnyConsensusState;
use crate::denom::DenomTrace;
use crate::error::Error;
use crate::event::source::{EventSource, TxEventSourceCmd};
use crate::event::IbcEventWithHeight;
use crate::keyring::{KeyRing, NamadaKeyPair, SigningKeyPair};
use crate::light_client::tendermint::LightClient as TmLightClient;
use crate::light_client::{LightClient, Verified};
use crate::misbehaviour::MisbehaviourEvidence;

use self::error::Error as NamadaError;

pub mod error;
pub mod key;
mod query;
mod tx;
pub mod wallet;

pub struct NamadaChain {
    /// Reuse CosmosSdkConfig for tendermint's light clients
    config: CosmosSdkConfig,
    /// Namada context
    ctx: NamadaImpl<HttpClient, wallet::NullWalletUtils, FsShieldedUtils, NullIo>,
    light_client: TmLightClient,
    rt: Arc<TokioRuntime>,
    keybase: KeyRing<NamadaKeyPair>,
    tx_monitor_cmd: Option<TxEventSourceCmd>,
}

impl NamadaChain {
    fn config(&self) -> &CosmosSdkConfig {
        &self.config
    }

    fn init_event_source(&mut self) -> Result<TxEventSourceCmd, Error> {
        crate::time!(
            "init_event_source",
            {
                "src_chain": self.config().id.to_string(),
            }
        );

        let node_info = self
            .rt
            .block_on(fetch_node_info(self.ctx.client(), &self.config))?;
        let compat_mode = CompatMode::from_version(node_info.version).unwrap_or(CompatMode::V0_37);

        use crate::config::EventSourceMode as Mode;
        let (event_source, monitor_tx) = match &self.config.event_source {
            Mode::Push { url, batch_delay } => EventSource::websocket(
                self.config.id.clone(),
                url.clone(),
                compat_mode,
                *batch_delay,
                self.rt.clone(),
            ),
            Mode::Pull { interval } => EventSource::rpc(
                self.config.id.clone(),
                self.ctx.client().clone(),
                *interval,
                self.rt.clone(),
            ),
        }
        .map_err(Error::event_source)?;

        thread::spawn(move || event_source.run());

        Ok(monitor_tx)
    }

    fn get_unbonding_time(&self) -> Result<Duration, Error> {
        let key = pos_storage_key::params_key();
        let (value, _) = self.query(key, QueryHeight::Latest, IncludeProof::No)?;
        let pos_params =
            OwnedPosParams::try_from_slice(&value[..]).map_err(NamadaError::borsh_decode)?;

        let key = param_storage::get_epoch_duration_storage_key();
        let (value, _) = self.query(key, QueryHeight::Latest, IncludeProof::No)?;
        let epoch_duration =
            EpochDuration::try_from_slice(&value[..]).map_err(NamadaError::borsh_decode)?;
        let unbonding_period = pos_params.pipeline_len * epoch_duration.min_duration.0;
        Ok(Duration::from_secs(unbonding_period))
    }

    fn get_latest_block_time(&self) -> Result<Time, Error> {
        let status = self
            .rt
            .block_on(SdkClient::status(self.ctx.client()))
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;
        Ok(status
            .sync_info
            .latest_block_time
            .to_string()
            .parse()
            .unwrap())
    }

    async fn shielded_sync(&self) -> Result<(), Error> {
        let mut shielded = self.ctx.shielded_mut().await;
        let _ = shielded.load().await;
        shielded
            .fetch(
                self.ctx.client(),
                &DefaultLogger::new(self.ctx.io()),
                None,
                None,
                1,
                &[],
                &[],
            )
            .await
            .map_err(NamadaError::namada)?;
        shielded.save().await.map_err(Error::io)
    }
}

impl ChainEndpoint for NamadaChain {
    type LightBlock = TMLightBlock;
    type Header = TmHeader;
    type ConsensusState = TmConsensusState;
    type ClientState = TmClientState;
    type Time = Time;
    type SigningKeyPair = NamadaKeyPair;

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn config(&self) -> ChainConfig {
        ChainConfig::Namada(self.config.clone())
    }

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        #[allow(irrefutable_let_patterns)]
        let ChainConfig::Namada(config) = config
        else {
            return Err(Error::config(ConfigError::wrong_type()));
        };

        let mut rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;
        rpc_client.set_compat_mode(CompatMode::V0_37);

        let node_info = rt.block_on(fetch_node_info(&rpc_client, &config))?;
        let light_client = TmLightClient::from_cosmos_sdk_config(&config, node_info.id)?;

        let keybase =
            KeyRing::new_namada(config.key_store_type, &config.id, &config.key_store_folder)
                .map_err(Error::key_base)?;

        let shielded_dir = dirs_next::home_dir()
            .expect("No home directory")
            .join(".hermes/shielded")
            .join(config.id.to_string());
        std::fs::create_dir_all(&shielded_dir).map_err(Error::io)?;
        let shielded_ctx = FsShieldedUtils::new(shielded_dir);

        let mut store = Store::default();
        let key = keybase
            .get_key(&config.key_name)
            .map_err(|e| Error::key_not_found(config.key_name.clone(), e))?;
        store.insert_keypair::<wallet::NullWalletUtils>(
            config.key_name.clone().into(),
            key.secret_key,
            None,
            Some(key.address),
            None,
            true,
        );
        let wallet = Wallet::new(wallet::NullWalletUtils, store);

        let native_token = rt
            .block_on(rpc::query_native_token(&rpc_client))
            .map_err(NamadaError::namada)?;

        // overwrite the proof spec
        let config = CosmosSdkConfig {
            proof_specs: Some(ibc_proof_specs::<Sha256Hasher>().into()),
            ..config
        };

        let ctx = NamadaImpl::native_new(rpc_client, wallet, shielded_ctx, NullIo, native_token);

        Ok(Self {
            config,
            ctx,
            light_client,
            rt,
            keybase,
            tx_monitor_cmd: None,
        })
    }

    fn shutdown(self) -> Result<(), Error> {
        Ok(())
    }

    fn health_check(&mut self) -> Result<HealthCheck, Error> {
        self.rt
            .block_on(SdkClient::health(self.ctx.client()))
            .map_err(|e| {
                Error::health_check_json_rpc(
                    self.config.id.clone(),
                    self.config.rpc_addr.to_string(),
                    "/health".to_string(),
                    e,
                )
            })?;

        Ok(HealthCheck::Healthy)
    }

    fn subscribe(&mut self) -> Result<Subscription, Error> {
        let tx_monitor_cmd = match &self.tx_monitor_cmd {
            Some(tx_monitor_cmd) => tx_monitor_cmd,
            None => {
                let tx_monitor_cmd = self.init_event_source()?;
                self.tx_monitor_cmd = Some(tx_monitor_cmd);
                self.tx_monitor_cmd.as_ref().unwrap()
            }
        };

        let subscription = tx_monitor_cmd.subscribe().map_err(Error::event_source)?;
        Ok(subscription)
    }

    fn keybase(&self) -> &KeyRing<Self::SigningKeyPair> {
        &self.keybase
    }

    fn keybase_mut(&mut self) -> &mut KeyRing<Self::SigningKeyPair> {
        &mut self.keybase
    }

    fn get_key(&self) -> Result<Self::SigningKeyPair, Error> {
        self.keybase
            .get_key(&self.config.key_name)
            .map_err(|e| Error::key_not_found(self.config.key_name.clone(), e))
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        let key = self
            .keybase
            .get_key(&self.config.key_name)
            .map_err(|e| Error::key_not_found(self.config.key_name.clone(), e))?;
        Ok(Signer::from_str(&key.account()).expect("The key name shouldn't be empty"))
    }

    fn version_specs(&self) -> Result<Specs, Error> {
        unimplemented!()
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!("send_messages_and_wait_commit");

        let proto_msgs = tracked_msgs.messages();
        if proto_msgs.is_empty() {
            return Ok(vec![]);
        }
        let mut tx_sync_results = vec![];
        for msg in proto_msgs.iter() {
            let response = self.send_tx(msg)?;

            // Note: we don't have any height information in this case. This hack will fix itself
            // once we remove the `ChainError` event (which is not actually an event)
            let height = ICSHeight::new(self.config.id.version(), 1).unwrap();
            let events_per_tx = vec![IbcEventWithHeight::new(IbcEvent::ChainError(format!(
                "check_tx (broadcast_tx_sync) on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
                self.config.id, response.hash, response.code, response.log
            )), height)];

            tx_sync_results.push(TxSyncResult {
                response,
                events: events_per_tx,
                status: TxStatus::Pending { message_count: 1 },
            });
        }

        self.wait_for_block_commits(&mut tx_sync_results)?;

        let events: Vec<IbcEventWithHeight> = tx_sync_results
            .into_iter()
            .flat_map(|el| el.events)
            .collect();
        let mut dedup_events = vec![];
        for event in events {
            if !dedup_events.contains(&event) {
                dedup_events.push(event);
            }
        }

        Ok(dedup_events)
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<Response>, Error> {
        crate::time!("send_messages_and_wait_check_tx");

        let proto_msgs = tracked_msgs.messages();
        if proto_msgs.is_empty() {
            return Ok(vec![]);
        }
        let mut responses = vec![];
        for msg in proto_msgs.iter() {
            responses.push(self.send_tx(msg)?);
        }

        Ok(responses)
    }

    fn verify_header(
        &mut self,
        trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        crate::time!(
            "verify_header",
            {
                "src_chain": self.config().id.to_string(),
            }
        );

        let now = self.get_latest_block_time()?;
        self.light_client
            .verify(trusted, target, client_state, now)
            .map(|v| v.target)
    }

    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        crate::time!(
            "check_misbehaviour",
            {
                "src_chain": self.config().id.to_string(),
            }
        );

        let now = self.get_latest_block_time()?;
        self.light_client
            .detect_misbehaviour(update, client_state, now)
    }

    fn query_balance(&self, key_name: Option<&str>, denom: Option<&str>) -> Result<Balance, Error> {
        // Given key_name and denom should be raw Namada addresses
        let default_owner = self.get_signer()?;
        let owner = key_name.unwrap_or(default_owner.as_ref());
        let owner =
            Address::decode(owner).map_err(|_| NamadaError::address_decode(owner.to_string()))?;

        let default_token = self.ctx.native_token().to_string();
        let denom = denom.unwrap_or(&default_token);
        let token =
            Address::decode(denom).map_err(|_| NamadaError::address_decode(denom.to_string()))?;

        let balance_key = balance_key(&token, &owner);
        let (value, _) = self.query(balance_key, QueryHeight::Latest, IncludeProof::No)?;
        if value.is_empty() {
            return Ok(Balance {
                amount: "0".to_string(),
                denom: denom.to_string(),
            });
        }
        let amount = Amount::try_from_slice(&value[..]).map_err(NamadaError::borsh_decode)?;
        let denom_key = denom_key(&token);
        let (value, _) = self.query(denom_key, QueryHeight::Latest, IncludeProof::No)?;
        let denominated_amount = if value.is_empty() {
            DenominatedAmount::new(amount, 0.into())
        } else {
            let token_denom =
                Denomination::try_from_slice(&value[..]).map_err(NamadaError::borsh_decode)?;
            DenominatedAmount::new(amount, token_denom)
        };

        Ok(Balance {
            amount: denominated_amount.to_string(),
            denom: denom.to_string(),
        })
    }

    fn query_all_balances(&self, key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        let default_owner = self.get_signer()?;
        let owner = key_name.unwrap_or(default_owner.as_ref());
        let owner =
            Address::decode(owner).map_err(|_| NamadaError::address_decode(owner.to_string()))?;

        let mut balances = vec![];
        let prefix = Key::from(Address::Internal(InternalAddress::Multitoken).to_db_key());
        for PrefixValue { key, value } in self.query_prefix(prefix)? {
            if let Some([token, bal_owner]) = is_any_token_balance_key(&key) {
                if owner == *bal_owner {
                    let amount =
                        Amount::try_from_slice(&value[..]).map_err(NamadaError::borsh_decode)?;
                    let denom_key = denom_key(token);
                    let (value, _) =
                        self.query(denom_key, QueryHeight::Latest, IncludeProof::No)?;
                    let denominated_amount = if value.is_empty() {
                        DenominatedAmount::new(amount, 0.into())
                    } else {
                        let namada_denom = Denomination::try_from_slice(&value[..])
                            .map_err(NamadaError::borsh_decode)?;
                        DenominatedAmount::new(amount, namada_denom)
                    };
                    let balance = Balance {
                        amount: denominated_amount.to_string(),
                        denom: token.to_string(),
                    };
                    balances.push(balance);
                }
            }
        }
        Ok(balances)
    }

    // Query the denom trace with "{IbcToken}" address which has a hashed denom.
    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        let denom = self.query_denom(hash)?;
        match denom.rsplit_once('/') {
            Some((path, base_denom)) => Ok(DenomTrace {
                path: path.to_string(),
                base_denom: base_denom.to_string(),
            }),
            None => Err(Error::query(format!(
                "The denom is not a PrefixedDenom: denom {}",
                denom
            ))),
        }
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        crate::time!(
            "query_commitment_prefix",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_commitment_prefix");

        CommitmentPrefix::try_from(b"ibc".to_vec()).map_err(Error::ics23)
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        crate::time!(
            "query_application_status",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_application_status");

        let status = self
            .rt
            .block_on(SdkClient::status(self.ctx.client()))
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        if status.sync_info.catching_up {
            return Err(Error::chain_not_caught_up(
                self.config.rpc_addr.to_string(),
                self.config().id.clone(),
            ));
        }

        let time = self.get_latest_block_time()?;
        let height = ICSHeight::new(
            ChainId::chain_version(status.node_info.network.as_str()),
            u64::from(status.sync_info.latest_block_height),
        )
        .map_err(Error::ics02)?;

        Ok(ChainStatus {
            height,
            timestamp: time.into(),
        })
    }

    fn query_clients(
        &self,
        _request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        crate::time!(
            "query_clients",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_clients");

        let prefix = storage::ibc_key("clients").expect("the path should be parsable");
        let mut states = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value } = prefix_value;
            if key.to_string().ends_with("clientState") {
                let client_id =
                    storage::client_id(&key).map_err(|e| Error::query(e.to_string()))?;
                let client_id = ClientId::from_str(&client_id.to_string()).unwrap();
                let client_state = AnyClientState::decode_vec(&value).map_err(Error::decode)?;
                states.push(IdentifiedAnyClientState::new(client_id, client_state));
            }
        }

        Ok(states)
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        crate::time!(
            "query_client_state",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_client_state");

        let path = ClientStatePath(request.client_id);
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        let (value, proof) = self.query(key, request.height, include_proof)?;
        let client_state = AnyClientState::decode_vec(&value).map_err(Error::decode)?;

        Ok((client_state, proof))
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        crate::time!(
            "query_consensus_state",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_consensus_state");

        let path = ClientConsensusStatePath {
            client_id: request.client_id,
            epoch: request.consensus_height.revision_number(),
            height: request.consensus_height.revision_height(),
        };
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        let (value, proof) = self.query(key, request.query_height, include_proof)?;
        let consensus_state = AnyConsensusState::decode_vec(&value).map_err(Error::decode)?;
        Ok((consensus_state, proof))
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<ICSHeight>, Error> {
        let prefix = storage::ibc_key(format!("clients/{}", request.client_id))
            .expect("the path should be parsable");
        let mut heights = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value: _ } = prefix_value;
            match storage::consensus_height(&key) {
                Ok(h) => {
                    let height = ICSHeight::new(h.revision_number(), h.revision_height()).unwrap();
                    heights.push(height);
                }
                // the key is not for a consensus state
                Err(_) => continue,
            }
        }
        Ok(heights)
    }

    fn query_upgraded_client_state(
        &self,
        _request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        crate::time!(
            "query_upgraded_client_state",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_upgraded_client_state");

        unimplemented!()
    }

    fn query_upgraded_consensus_state(
        &self,
        _request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        crate::time!(
            "query_upgraded_consensus_state",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_upgraded_consensus_state");

        unimplemented!()
    }

    fn query_connections(
        &self,
        _request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        crate::time!(
            "query_connections",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_connections");

        let prefix = storage::ibc_key("connections").expect("the path should be parsable");
        let mut connections = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value } = prefix_value;
            // "connections/counter" should be skipped
            if key == storage::connection_counter_key() {
                continue;
            }
            let conn_id = storage::connection_id(&key).map_err(|e| Error::query(e.to_string()))?;
            let connection_id = conn_id
                .as_str()
                .parse()
                .expect("The connection ID should be parsable");
            let connection = ConnectionEnd::decode_vec(&value).map_err(Error::decode)?;
            connections.push(IdentifiedConnectionEnd::new(connection_id, connection));
        }

        Ok(connections)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        crate::time!(
            "query_client_connections",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_client_connections");

        let query_request = QueryConnectionsRequest { pagination: None };
        let connections = self.query_connections(query_request)?;
        let ids = connections
            .iter()
            .filter(|c| *c.connection_end.client_id() == request.client_id)
            .map(|c| c.connection_id.clone())
            .collect();
        Ok(ids)
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        crate::time!(
            "query_connection",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_connection");

        let path = ConnectionsPath(request.connection_id);
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        let (value, proof) = self.query(key, request.height, include_proof)?;
        let connection_end = ConnectionEnd::decode_vec(&value).map_err(Error::decode)?;
        Ok((connection_end, proof))
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        crate::time!(
            "query_connection_channels",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_connection_channels");

        let hops = vec![request.connection_id];
        let query_request = QueryChannelsRequest { pagination: None };
        let channels = self
            .query_channels(query_request)?
            .into_iter()
            .filter(|c| c.channel_end.connection_hops_matches(&hops))
            .collect();

        Ok(channels)
    }

    fn query_channels(
        &self,
        _request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        crate::time!(
            "query_channels",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_channels");

        let prefix = storage::ibc_key("channelEnds").expect("the path should be parsable");
        let mut channels = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value } = prefix_value;
            // "channelEnds/counter" should be skipped
            if key == storage::channel_counter_key() {
                continue;
            }
            let (port_id, channel_id) =
                storage::port_channel_id(&key).map_err(|e| Error::query(e.to_string()))?;
            let port_id = port_id.as_ref().parse().unwrap();
            let channel_id = channel_id.as_ref().parse().unwrap();
            let channel = ChannelEnd::decode_vec(&value).map_err(Error::decode)?;
            channels.push(IdentifiedChannelEnd::new(port_id, channel_id, channel))
        }

        Ok(channels)
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        crate::time!(
            "query_channel",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_channel");

        let path = ChannelEndsPath(request.port_id, request.channel_id);
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        let (value, proof) = self.query(key, request.height, include_proof)?;
        let channel_end = ChannelEnd::decode_vec(&value).map_err(Error::decode)?;
        Ok((channel_end, proof))
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        crate::time!(
            "query_channel_client_state",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_channel_client_state");

        let request = QueryChannelRequest {
            port_id: request.port_id,
            channel_id: request.channel_id,
            height: QueryHeight::Latest,
        };
        let (channel_end, _) = self.query_channel(request, IncludeProof::No)?;
        let connection_id = channel_end
            .connection_hops()
            .first()
            .ok_or_else(|| Error::query("no connection ID in the channel end".to_string()))?
            .clone();
        let request = QueryConnectionRequest {
            connection_id,
            height: QueryHeight::Latest,
        };
        let (connection_end, _) = self.query_connection(request, IncludeProof::No)?;
        let client_id = connection_end.client_id().clone();
        let request = QueryClientStateRequest {
            client_id: client_id.clone(),
            height: QueryHeight::Latest,
        };
        let (client_state, _) = self.query_client_state(request, IncludeProof::No)?;

        Ok(Some(IdentifiedAnyClientState {
            client_id,
            client_state,
        }))
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let path = CommitmentsPath {
            port_id: request.port_id,
            channel_id: request.channel_id,
            sequence: request.sequence,
        };
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        self.query(key, request.height, include_proof)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        crate::time!(
            "query_packet_commitments",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_packet_commitments");

        let path = format!(
            "commitments/ports/{}/channels/{}/sequences",
            request.port_id, request.channel_id
        );
        let prefix = storage::ibc_key(path).expect("the path should be parsable");
        let mut sequences = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value: _ } = prefix_value;
            let (_, _, sequence) =
                storage::port_channel_sequence_id(&key).map_err(|e| Error::query(e.to_string()))?;
            let sequence = u64::from(sequence).into();
            sequences.push(sequence);
        }

        // NOTE the height might be mismatched with the previous query
        let status = self.query_application_status()?;

        Ok((sequences, status.height))
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let path = ReceiptsPath {
            port_id: request.port_id,
            channel_id: request.channel_id,
            sequence: request.sequence,
        };
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        self.query(key, request.height, include_proof)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        crate::time!(
            "query_unreceived_packets",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_unreceived_packets");

        let path = format!(
            "receipts/ports/{}/channels/{}/sequences",
            request.port_id, request.channel_id
        );
        let prefix = storage::ibc_key(path).expect("the path should be parsable");
        let mut received_seqs = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let (_, _, sequence) = storage::port_channel_sequence_id(&prefix_value.key)
                .map_err(|e| Error::query(e.to_string()))?;
            let sequence = u64::from(sequence).into();
            received_seqs.push(sequence)
        }

        let unreceived_seqs = request
            .packet_commitment_sequences
            .into_iter()
            .filter(|seq| !received_seqs.contains(seq))
            .collect();

        Ok(unreceived_seqs)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let path = AcksPath {
            port_id: request.port_id,
            channel_id: request.channel_id,
            sequence: request.sequence,
        };
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        self.query(key, request.height, include_proof)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        crate::time!(
            "query_packet_acknowledgements",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_packet_acknowledgements");

        let path = format!(
            "acks/ports/{}/channels/{}/sequences",
            request.port_id, request.channel_id
        );
        let prefix = storage::ibc_key(path).expect("the path should be parsable");
        let mut sequences = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value: _ } = prefix_value;
            let (_, _, sequence) =
                storage::port_channel_sequence_id(&key).map_err(|e| Error::query(e.to_string()))?;
            let sequence = u64::from(sequence).into();
            if request.packet_commitment_sequences.contains(&sequence) {
                sequences.push(sequence);
            }
        }

        // NOTE the height might be mismatched with the previous query
        let status = self.query_application_status()?;
        Ok((sequences, status.height))
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        crate::time!(
            "query_unreceived_acknowledgements",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_unreceived_acknowledgements");

        let path = format!(
            "commitments/ports/{}/channels/{}/sequences",
            request.port_id, request.channel_id
        );
        let prefix = storage::ibc_key(path).expect("the path should be parsable");
        let mut unreceived_seqs = vec![];
        for prefix_value in self.query_prefix(prefix)? {
            let PrefixValue { key, value: _ } = prefix_value;
            let (_, _, sequence) =
                storage::port_channel_sequence_id(&key).map_err(|e| Error::query(e.to_string()))?;
            let sequence = u64::from(sequence).into();
            if request.packet_ack_sequences.contains(&sequence) {
                unreceived_seqs.push(sequence);
            }
        }
        Ok(unreceived_seqs)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        crate::time!(
            "query_next_sequence_receive",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_next_sequence_receive");

        let path = SeqRecvsPath(request.port_id, request.channel_id);
        let key = storage::ibc_key(path.to_string()).expect("the path should be parsable");
        let (value, proof) = self.query(key, request.height, include_proof)?;

        // As ibc-go, the sequence index is encoded with big-endian
        let index: [u8; 8] = value
            .try_into()
            .map_err(|_| Error::query("Encoding u64 failed".to_owned()))?;
        let sequence = u64::from_be_bytes(index).into();

        Ok((sequence, proof))
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!("query_txs",
        {
            "src_chain": self.config().id.to_string(),
        });
        crate::telemetry!(query, self.id(), "query_txs");

        match request {
            QueryTxRequest::Client(request) => {
                crate::time!("query_txs: single client update event");
                match self.query_update_event(&request)? {
                    Some(event) => Ok(vec![event]),
                    None => Ok(vec![]),
                }
            }
            QueryTxRequest::Transaction(tx) => self.query_tx_events(&tx.0.to_string()),
        }
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!(
            "query_packet_events",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_packet_events");
        self.query_packet_events_from_block(&request)
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        let height = match request.height {
            QueryHeight::Latest => TmHeight::from(0u32),
            QueryHeight::Specific(ibc_height) => {
                TmHeight::try_from(ibc_height.revision_height()).map_err(Error::invalid_height)?
            }
        };

        let rpc_call = match height.value() {
            0 => SdkClient::latest_block(self.ctx.client()),
            _ => SdkClient::block(self.ctx.client(), height),
        };
        let response = self
            .rt
            .block_on(rpc_call)
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;
        Ok(Self::ConsensusState::from(response.block.header))
    }

    fn build_client_state(
        &self,
        height: ICSHeight,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        let ClientSettings::Tendermint(settings) = settings;
        let unbonding_period = self.get_unbonding_time()?;
        let trusting_period = settings.trusting_period.unwrap_or_else(|| {
            self.config
                .trusting_period
                .unwrap_or(2 * unbonding_period / 3)
        });
        TmClientState::new(
            self.id().clone(),
            settings.trust_threshold,
            trusting_period,
            unbonding_period,
            settings.max_clock_drift,
            height,
            self.config.proof_specs.clone().unwrap(),
            vec![],
            AllowUpdate {
                after_expiry: true,
                after_misbehaviour: true,
            },
        )
        .map_err(Error::ics07)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        crate::time!(
            "build_consensus_state",
            {
                "src_chain": self.config().id.to_string(),
            }
        );

        Ok(TmConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &mut self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        crate::time!(
            "build_header",
            {
                "src_chain": self.config().id.to_string(),
            }
        );

        let now = self.get_latest_block_time()?;
        // Get the light block at target_height from chain.
        let Verified { target, supporting } = self.light_client.header_and_minimal_set(
            trusted_height,
            target_height,
            client_state,
            now,
        )?;

        Ok((target, supporting))
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        _channel_id: &ChannelId,
        _port_id: &PortId,
        _counterparty_payee: &Signer,
    ) -> Result<(), Error> {
        // not supported
        unimplemented!()
    }

    fn cross_chain_query(
        &self,
        _requests: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error> {
        // not supported
        unimplemented!()
    }

    fn query_incentivized_packet(
        &self,
        _request: QueryIncentivizedPacketRequest,
    ) -> Result<QueryIncentivizedPacketResponse, Error> {
        // not supported
        unimplemented!()
    }

    fn query_consumer_chains(&self) -> Result<Vec<(ChainId, ClientId)>, Error> {
        // not supported
        unimplemented!()
    }
}

/// Fetch the node info
async fn fetch_node_info(
    rpc_client: &HttpClient,
    config: &CosmosSdkConfig,
) -> Result<node::Info, Error> {
    crate::time!("fetch_node_info",
    {
        "src_chain": config.id.to_string(),
    });

    Client::status(rpc_client)
        .await
        .map(|s| s.node_info)
        .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))
}
