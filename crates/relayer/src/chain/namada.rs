use alloc::sync::Arc;
use core::str::FromStr;
use std::thread;

use core::time::Duration;
use std::path::Path;

use borsh::BorshDeserialize;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{
    QueryIncentivizedPacketRequest, QueryIncentivizedPacketResponse,
};
use ibc_proto::protobuf::Protobuf;
use ibc_relayer_types::applications::ics31_icq::response::CrossChainQueryResponse;
use ibc_relayer_types::clients::ics07_tendermint::client_state::{AllowUpdate, ClientState};
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
use ibc_relayer_types::core::ics23_commitment::specs::ProofSpecs;
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
use namada::ledger::ibc::storage;
use namada::ledger::parameters::storage as param_storage;
use namada::ledger::parameters::EpochDuration;
use namada::ledger::storage::ics23_specs::ibc_proof_specs;
use namada::ledger::storage::Sha256Hasher;
use namada::ledger::wallet::Wallet;
use namada::proof_of_stake::parameters::PosParams;
use namada::proof_of_stake::storage as pos_storage;
use namada::tendermint::block::Height as TmHeight;
use namada::tendermint_rpc::{Client, HttpClient, Url};
use namada::types::address::{Address, InternalAddress};
use namada::types::storage::{Key, KeySeg, PrefixValue};
use namada::types::token;
use namada_apps::wallet::CliWalletUtils;
use prost::Message;
use tendermint::Time;
use tendermint_light_client::types::LightBlock as TMLightBlock;
use tendermint_rpc::client::CompatMode;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tokio::runtime::Runtime as TokioRuntime;

use crate::account::Balance;
use crate::chain::client::ClientSettings;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::handle::Subscription;
use crate::chain::requests::*;
use crate::chain::tracking::TrackedMsgs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::ChainConfig;
use crate::consensus_state::AnyConsensusState;
use crate::denom::DenomTrace;
use crate::error::Error;
use crate::event::source::{EventSource, TxEventSourceCmd};
use crate::event::IbcEventWithHeight;
use crate::keyring::{KeyRing, Secp256k1KeyPair};
use crate::light_client::tendermint::LightClient as TmLightClient;
use crate::light_client::LightClient;
use crate::light_client::Verified;
use crate::misbehaviour::MisbehaviourEvidence;

use crate::chain::endpoint::{ChainEndpoint, ChainStatus, HealthCheck};

const BASE_WALLET_DIR: &str = "namada_wallet";

pub mod query;
pub mod tx;

pub struct NamadaChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    light_client: TmLightClient,
    rt: Arc<TokioRuntime>,
    wallet: Wallet<CliWalletUtils>,
    keybase: KeyRing<Secp256k1KeyPair>,
    tx_monitor_cmd: Option<TxEventSourceCmd>,
}

impl NamadaChain {
    fn init_event_source(&mut self) -> Result<TxEventSourceCmd, Error> {
        crate::time!(
            "init_event_source",
            {
                "src_chain": self.config().id.to_string(),
            }
        );

        use crate::config::EventSourceMode as Mode;
        let rpc_client = tendermint_rpc::HttpClient::new(self.config.rpc_addr.clone())
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        let (event_source, monitor_tx) = match &self.config.event_source {
            Mode::Push { url, batch_delay } => EventSource::websocket(
                self.config.id.clone(),
                url.clone(),
                CompatMode::V0_34,
                *batch_delay,
                self.rt.clone(),
            ),
            Mode::Pull { interval } => EventSource::rpc(
                self.config.id.clone(),
                rpc_client,
                *interval,
                self.rt.clone(),
            ),
        }
        .map_err(Error::event_source)?;

        thread::spawn(move || event_source.run());

        Ok(monitor_tx)
    }

    fn get_unbonding_time(&self) -> Result<Duration, Error> {
        let key = pos_storage::params_key();
        let (value, _) = self.query(key, QueryHeight::Latest, IncludeProof::No)?;
        let pos_params = PosParams::try_from_slice(&value[..]).map_err(Error::borsh_decode)?;

        let key = param_storage::get_epoch_duration_storage_key();
        let (value, _) = self.query(key, QueryHeight::Latest, IncludeProof::No)?;
        let epoch_duration =
            EpochDuration::try_from_slice(&value[..]).map_err(Error::borsh_decode)?;
        let unbonding_period = pos_params.pipeline_len * epoch_duration.min_duration.0;
        Ok(Duration::from_secs(unbonding_period))
    }

    fn get_latest_block_time(&self) -> Result<Time, Error> {
        let status = self
            .rt
            .block_on(self.rpc_client.status())
            .map_err(|e| Error::abci_plus_rpc(self.config.rpc_addr.clone(), e))?;
        Ok(status
            .sync_info
            .latest_block_time
            .to_string()
            .parse()
            .unwrap())
    }
}

impl ChainEndpoint for NamadaChain {
    type LightBlock = TMLightBlock;
    type Header = TmHeader;
    type ConsensusState = TmConsensusState;
    type ClientState = ClientState;
    type Time = Time;
    type SigningKeyPair = Secp256k1KeyPair;

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let rpc_addr = Url::from_str(&config.rpc_addr.to_string()).unwrap();
        let rpc_client = HttpClient::new(rpc_addr)
            .map_err(|e| Error::abci_plus_rpc(config.rpc_addr.clone(), e))?;

        let light_client = rt.block_on(fetch_node_info(&rpc_client, &config))?;

        // not used in Anoma, but the trait requires KeyRing
        let keybase = KeyRing::new(
            config.key_store_type,
            &config.account_prefix,
            &config.id,
            &config.key_store_folder,
        )
        .map_err(Error::key_base)?;

        // check if the wallet has been set up for this relayer
        let wallet_path = Path::new(BASE_WALLET_DIR).join(config.id.to_string());
        let mut wallet = namada_apps::wallet::load(&wallet_path)
            .ok_or_else(Error::namada_wallet_not_initialized)?;
        wallet
            .find_key(&config.key_name, None)
            .map_err(Error::namada_key_pair_not_found)?;

        // overwrite the proof spec
        let config = ChainConfig {
            proof_specs: Some(get_proof_specs()),
            ..config
        };

        Ok(Self {
            config,
            rpc_client,
            light_client,
            rt,
            wallet,
            keybase,
            tx_monitor_cmd: None,
        })
    }

    fn shutdown(self) -> Result<(), Error> {
        Ok(())
    }

    fn health_check(&mut self) -> Result<HealthCheck, Error> {
        self.rt.block_on(self.rpc_client.health()).map_err(|e| {
            Error::abci_plus_health_check_json_rpc(
                self.config.id.clone(),
                self.config.rpc_addr.to_string(),
                "/health".to_string(),
                e,
            )
        })?;

        // TODO Namada health check

        // TODO version check

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

    fn get_signer(&self) -> Result<Signer, Error> {
        let address = self
            .wallet
            .find_address(&self.config.key_name)
            .ok_or_else(|| Error::namada_address_not_found(self.config.key_name.clone()))?;

        Ok(Signer::from_str(&address.to_string()).unwrap())
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
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
        let key_name = key_name.unwrap_or(&self.config.key_name);
        let denom = denom.unwrap_or(tx::FEE_TOKEN);
        let token = match self.wallet.find_address(denom) {
            Some(addr) => addr.clone(),
            None => Address::decode(denom)
                .map_err(|_| Error::namada_address_not_found(denom.to_string()))?,
        };

        let owner = self
            .wallet
            .find_address(key_name)
            .ok_or_else(|| Error::namada_address_not_found(key_name.to_string()))?;

        let balance_key = token::balance_key(&token, owner);
        let (value, _) = self.query(balance_key, QueryHeight::Latest, IncludeProof::No)?;
        if value.is_empty() {
            return Ok(Balance {
                amount: "0".to_string(),
                denom: denom.to_string(),
            });
        }
        let amount = token::Amount::try_from_slice(&value[..]).map_err(Error::borsh_decode)?;
        let denom_key = token::denom_key(&token);
        let (value, _) = self.query(denom_key, QueryHeight::Latest, IncludeProof::No)?;
        let denominated_amount = if value.is_empty() {
            token::DenominatedAmount::native(amount)
        } else {
            let token_denom =
                token::Denomination::try_from_slice(&value[..]).map_err(Error::borsh_decode)?;
            token::DenominatedAmount {
                amount,
                denom: token_denom,
            }
        };

        Ok(Balance {
            amount: denominated_amount.to_string(),
            denom: denom.to_string(),
        })
    }

    fn query_all_balances(&self, key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        let key_name = key_name.unwrap_or(&self.config.key_name);
        let key_owner = self
            .wallet
            .find_address(key_name)
            .ok_or_else(|| Error::namada_address_not_found(key_name.to_string()))?;

        let mut balances = vec![];
        let prefix = Key::from(Address::Internal(InternalAddress::Multitoken).to_db_key());
        for PrefixValue { key, value } in self.query_prefix(prefix)? {
            if let Some([token, owner]) = token::is_any_token_balance_key(&key) {
                if key_owner == owner {
                    let amount =
                        token::Amount::try_from_slice(&value[..]).map_err(Error::borsh_decode)?;
                    let denom_key = token::denom_key(token);
                    let (value, _) =
                        self.query(denom_key, QueryHeight::Latest, IncludeProof::No)?;
                    let denominated_amount = if value.is_empty() {
                        token::DenominatedAmount::native(amount)
                    } else {
                        let namada_denom = token::Denomination::try_from_slice(&value[..])
                            .map_err(Error::borsh_decode)?;
                        token::DenominatedAmount {
                            amount,
                            denom: namada_denom,
                        }
                    };
                    let alias = self
                        .wallet
                        .find_alias(token)
                        .map(|a| a.to_string())
                        .unwrap_or(token.to_string());
                    let balance = Balance {
                        amount: denominated_amount.to_string(),
                        denom: alias,
                    };
                    balances.push(balance);
                }
            }
        }
        Ok(balances)
    }

    // Query the denom trace with "{IbcToken}" address which has a hashed denom.
    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        let token = Address::decode(&hash)
            .map_err(|_| Error::namada_address_not_found(hash.to_string()))?;
        let key = match token {
            Address::Internal(InternalAddress::IbcToken(hash)) => storage::ibc_denom_key(hash),
            _ => return Err(Error::namada_address_not_found(token.to_string())),
        };
        let (value, _) = self.query(key, QueryHeight::Latest, IncludeProof::No)?;
        let denom = String::try_from_slice(&value[..]).map_err(|e| {
            Error::query(format!(
                "Decoding the original denom failed: denom {}, error {}",
                hash, e
            ))
        })?;

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
            .block_on(self.rpc_client.status())
            .map_err(|e| Error::abci_plus_rpc(self.config.rpc_addr.clone(), e))?;

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
            .get(0)
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
            QueryHeight::Specific(ibc_height) => TmHeight::try_from(ibc_height.revision_height())
                .map_err(Error::namada_tendermint)?,
        };

        // TODO(hu55a1n1): use the `/header` RPC endpoint instead when we move to tendermint v0.35.x
        let rpc_call = match height.value() {
            0 => self.rpc_client.latest_block(),
            _ => self.rpc_client.block(height),
        };
        let response = self
            .rt
            .block_on(rpc_call)
            .map_err(|e| Error::abci_plus_rpc(self.config.rpc_addr.clone(), e))?;
        // for the different tendermint-rs
        let cs = namada::ibc::clients::ics07_tendermint::consensus_state::ConsensusState::from(
            response.block.header,
        );
        let encoded = namada::ibc_proto::protobuf::Protobuf::<
            namada::ibc_proto::google::protobuf::Any,
        >::encode_vec(&cs);
        let consensus_state = Protobuf::<Any>::decode_vec(&encoded).unwrap();
        Ok(consensus_state)
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
        ClientState::new(
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
}

/// Initialize the light client
async fn fetch_node_info(
    rpc_client: &HttpClient,
    config: &ChainConfig,
) -> Result<TmLightClient, Error> {
    use tendermint_light_client::types::PeerId;

    crate::time!("fetch_node_info",
    {
        "src_chain": config.id.to_string(),
    });

    let peer_id = rpc_client
        .status()
        .await
        .map(|s| s.node_info.id)
        .map_err(|e| Error::abci_plus_rpc(config.rpc_addr.clone(), e))?;
    let bytes: [u8; 20] = peer_id
        .as_bytes()
        .try_into()
        .expect("the ID should be the same length");
    let peer_id = PeerId::new(bytes);
    let light_client = TmLightClient::from_config(config, peer_id)?;

    Ok(light_client)
}

/// convert ProofSpec for ics23 0.10.0
fn get_proof_specs() -> ProofSpecs {
    use ics23::ProofSpec;
    let proof_specs: Vec<ProofSpec> = ibc_proof_specs::<Sha256Hasher>()
        .iter()
        .map(|proof_spec| {
            let buf = proof_spec.encode_to_vec();
            ics23::ProofSpec::decode(&buf[..]).unwrap()
        })
        .collect();
    proof_specs.into()
}