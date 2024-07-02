use alloc::sync::Arc;
use std::{
    str::FromStr as _,
    time::Duration,
};

use ibc_proto::ibc::{
    apps::fee::v1::{
        QueryIncentivizedPacketRequest,
        QueryIncentivizedPacketResponse,
    },
    core::{
        channel::v1::query_client::QueryClient as IbcChannelQueryClient,
        client::v1::query_client::QueryClient as IbcClientQueryClient,
        connection::v1::query_client::QueryClient as IbcConnectionQueryClient,
    },
};
use ibc_relayer_types::{
    applications::ics31_icq::response::CrossChainQueryResponse,
    clients::ics07_tendermint::{
        client_state::ClientState as TendermintClientState,
        consensus_state::ConsensusState as TendermintConsensusState,
        header::Header,
    },
    core::{
        ics02_client::{
            client_type::ClientType,
            events::UpdateClient,
        },
        ics03_connection::connection::{
            ConnectionEnd,
            IdentifiedConnectionEnd,
        },
        ics04_channel::{
            channel::{
                ChannelEnd,
                IdentifiedChannelEnd,
            },
            packet::Sequence,
        },
        ics23_commitment::{
            commitment::CommitmentPrefix,
            merkle::MerkleProof,
        },
        ics24_host::identifier::{
            ChainId,
            ChannelId,
            ClientId,
            ConnectionId,
            PortId,
        },
    },
    signer::Signer,
    Height as ICSHeight,
};
use prost::Message;
use tendermint::time::Time as TmTime;
use tendermint_light_client::verifier::types::LightBlock;
use tendermint_rpc::{
    client::CompatMode,
    endpoint::{
        broadcast::tx_sync::Response as TxResponse,
        status,
    },
    Client as _,
    HttpClient,
};
use tokio::runtime::Runtime as TokioRuntime;
use tonic::IntoRequest;
use tracing::warn;

use crate::{
    account::Balance,
    chain::{
        astria::utils::{
            decode_merkle_proof,
            response_to_tx_sync_result,
        },
        client::ClientSettings,
        cosmos::{
            version::Specs,
            wait::wait_for_block_commits,
        },
        endpoint::{
            ChainEndpoint,
            ChainStatus,
            HealthCheck,
        },
        handle::Subscription,
        requests::*,
        tracking::TrackedMsgs,
    },
    client_state::{
        AnyClientState,
        IdentifiedAnyClientState,
    },
    config::ChainConfig,
    consensus_state::AnyConsensusState,
    denom::DenomTrace,
    error::Error,
    event::{
        source::{
            EventSource,
            TxEventSourceCmd,
        },
        IbcEventWithHeight,
    },
    keyring::{
        Ed25519KeyPair,
        KeyRing,
    },
    light_client::{
        tendermint::LightClient,
        LightClient as _,
    },
    misbehaviour::MisbehaviourEvidence,
};

const DEFAULT_RPC_TIMEOUT: Duration = Duration::from_secs(60);

pub struct AstriaEndpoint {
    config: ChainConfig,
    keybase: KeyRing<Ed25519KeyPair>,
    sequencer_client: HttpClient,
    compat_mode: CompatMode,
    light_client: LightClient,
    /// gRPC client for sequencer app
    ibc_client_grpc_client: IbcClientQueryClient<tonic::transport::Channel>,
    ibc_connection_grpc_client: IbcConnectionQueryClient<tonic::transport::Channel>,
    ibc_channel_grpc_client: IbcChannelQueryClient<tonic::transport::Channel>,
    rt: Arc<TokioRuntime>,
    tx_monitor_cmd: Option<TxEventSourceCmd>,
}

impl AstriaEndpoint {
    pub fn new(
        config: ChainConfig,
        keybase: KeyRing<Ed25519KeyPair>,
        rt: Arc<TokioRuntime>,
    ) -> Result<Self, Error> {
        let mut sequencer_client =
            HttpClient::new(config.rpc_addr().clone()).map_err(|e| Error::other(e.into()))?;

        let cosmos_config = match &config {
            ChainConfig::Astria(c) => c,
            _ => {
                println!("Wrong chain configuration type in AstriaEndpoint::bootstrap");
                return Err(Error::config(crate::config::ConfigError::wrong_type()));
            }
        };

        use crate::chain::cosmos::fetch_node_info;
        let node_info = rt.block_on(fetch_node_info(&sequencer_client, cosmos_config))?;

        let compat_mode = CompatMode::from_version(node_info.version).unwrap_or_else(|e| {
            warn!("Unsupported tendermint version, will use v0.37 compatibility mode but relaying might not work as desired: {e}");
            CompatMode::V0_37
        });
        sequencer_client.set_compat_mode(compat_mode);

        let light_client = LightClient::from_cosmos_sdk_config(cosmos_config, node_info.id)?;

        use http::Uri;
        let grpc_addr = Uri::from_str(&cosmos_config.grpc_addr.to_string())
            .map_err(|e| Error::invalid_uri(cosmos_config.grpc_addr.to_string(), e))?;
        let ibc_client_grpc_client = rt
            .block_on(IbcClientQueryClient::connect(grpc_addr.clone()))
            .map_err(Error::grpc_transport)?
            .max_decoding_message_size(config.max_grpc_decoding_size().get_bytes() as usize);
        let ibc_connection_grpc_client = rt
            .block_on(IbcConnectionQueryClient::connect(grpc_addr.clone()))
            .map_err(Error::grpc_transport)?
            .max_decoding_message_size(config.max_grpc_decoding_size().get_bytes() as usize);
        let ibc_channel_grpc_client = rt
            .block_on(IbcChannelQueryClient::connect(grpc_addr))
            .map_err(Error::grpc_transport)?
            .max_decoding_message_size(config.max_grpc_decoding_size().get_bytes() as usize);

        Ok(Self {
            config,
            keybase,
            sequencer_client,
            compat_mode,
            light_client,
            ibc_client_grpc_client,
            ibc_connection_grpc_client,
            ibc_channel_grpc_client,
            rt,
            tx_monitor_cmd: None,
        })
    }

    fn chain_status(&self) -> Result<status::Response, Error> {
        let status = self
            .rt
            .block_on(self.sequencer_client.status())
            .map_err(|e| Error::rpc(self.config.rpc_addr().clone(), e))?;

        Ok(status)
    }
}

impl AstriaEndpoint {
    fn block_on<T>(&self, fut: impl std::future::Future<Output = T>) -> T {
        self.rt.block_on(fut)
    }

    fn init_event_source(&mut self) -> Result<TxEventSourceCmd, Error> {
        use crate::config::EventSourceMode as Mode;

        let (event_source, monitor_tx) = match &self.config.event_source_mode() {
            Mode::Push { url, batch_delay } => EventSource::websocket(
                self.id().clone(),
                url.clone(),
                self.compat_mode,
                *batch_delay,
                self.rt.clone(),
            ),
            Mode::Pull { interval } => EventSource::rpc(
                self.id().clone(),
                self.sequencer_client.clone(),
                *interval,
                self.rt.clone(),
            ),
        }
        .map_err(Error::event_source)?;

        std::thread::spawn(move || event_source.run());
        Ok(monitor_tx)
    }

    async fn broadcast_messages(&mut self, tracked_msgs: TrackedMsgs) -> Result<TxResponse, Error> {
        use astria_core::{
            crypto::{
                SigningKey,
                VerificationKey,
            },
            generated::protocol::transaction::v1alpha1::Ics20Withdrawal as RawIcs20Withdrawal,
            primitive::v1::Address,
            protocol::transaction::v1alpha1::{
                action::Ics20Withdrawal,
                Action,
                TransactionParams,
                UnsignedTransaction,
            },
        };
        use astria_sequencer_client::SequencerClientExt as _;
        use ibc_relayer_types::applications::transfer::msgs::ASTRIA_WITHDRAWAL_TYPE_URL;
        use penumbra_ibc::IbcRelay;
        use penumbra_proto::core::component::ibc::v1::IbcRelay as RawIbcRelay;

        let msg_len = tracked_msgs.msgs.len();
        let mut actions: Vec<Action> = Vec::with_capacity(msg_len);
        for msg in tracked_msgs.msgs {
            if msg.type_url == ASTRIA_WITHDRAWAL_TYPE_URL {
                let action = RawIcs20Withdrawal::decode(msg.value.as_slice())
                    .map_err(|e| Error::other(e.into()))?;
                let non_raw =
                    Ics20Withdrawal::try_from_raw(action).map_err(|e| Error::other(e.into()))?;
                actions.push(Action::Ics20Withdrawal(non_raw));
                continue;
            }

            let ibc_action = RawIbcRelay {
                raw_action: Some(pbjson_types::Any {
                    type_url: msg.type_url,
                    value: msg.value.into(),
                }),
            };
            let non_raw = IbcRelay::try_from(ibc_action).map_err(|e| Error::other(e.into()))?;
            actions.push(Action::Ibc(non_raw));
        }

        let signing_key: ed25519_consensus::SigningKey =
            (*self.get_key()?.signing_key().as_bytes()).into(); // TODO cache this
        let verification_key = VerificationKey::try_from(signing_key.verification_key().to_bytes())
            .map_err(|e| Error::other(e.into()))?;
        let address = Address::builder()
            .verification_key(&verification_key)
            .prefix("astria")
            .try_build()
            .map_err(|e| Error::other(e.into()))?;
        let nonce = self
            .sequencer_client
            .get_latest_nonce(address)
            .await
            .map_err(|e| Error::other(Box::new(e)))?;

        let unsigned_tx = UnsignedTransaction {
            params: TransactionParams::builder()
                .nonce(nonce.nonce)
                .chain_id(self.id().to_string())
                .build(),
            actions,
        };

        let signed_tx = unsigned_tx.into_signed(&SigningKey::from(signing_key.to_bytes()));
        let tx_bytes = signed_tx.into_raw().encode_to_vec();

        let resp = self
            .sequencer_client
            .broadcast_tx_sync(tx_bytes)
            .await
            .map_err(|e| Error::other(e.into()))?;
        Ok(resp)
    }

    async fn query_packets_from_blocks(
        &self,
        request: &QueryPacketEventDataRequest,
    ) -> Result<(Vec<IbcEventWithHeight>, Vec<IbcEventWithHeight>), Error> {
        use crate::chain::cosmos::query::packet_query;

        let mut begin_block_events = vec![];
        let mut end_block_events = vec![];

        for seq in request.sequences.iter().copied() {
            let response = self
                .sequencer_client
                .block_search(
                    packet_query(request, seq),
                    // We only need the first page
                    1,
                    // There should only be a single match for this query, but due to
                    // the fact that the indexer treat the query as a disjunction over
                    // all events in a block rather than a conjunction over a single event,
                    // we may end up with partial matches and therefore have to account for
                    // that by fetching multiple results and filter it down after the fact.
                    // In the worst case we get N blocks where N is the number of channels,
                    // but 10 seems to work well enough in practice while keeping the response
                    // size, and therefore pressure on the node, fairly low.
                    10,
                    // We could pick either ordering here, since matching blocks may be at pretty
                    // much any height relative to the target blocks, so we went with most recent
                    // blocks first.
                    tendermint_rpc::Order::Descending,
                )
                .await
                .map_err(|e| Error::rpc(self.config.rpc_addr().clone(), e))?;

            for block in response.blocks.into_iter().map(|response| response.block) {
                let response_height =
                    ICSHeight::new(self.id().version(), u64::from(block.header.height))
                        .map_err(|_| Error::invalid_height_no_source())?;

                if let QueryHeight::Specific(query_height) = request.height.get() {
                    if response_height > query_height {
                        continue;
                    }
                }

                // `query_packet_from_block` retrieves the begin and end block events
                // and filter them to retain only those matching the query
                let (new_begin_block_events, new_end_block_events) =
                    self.query_packet_from_block(request, &[seq], &response_height)?;

                begin_block_events.extend(new_begin_block_events);
                end_block_events.extend(new_end_block_events);
            }
        }

        Ok((begin_block_events, end_block_events))
    }

    pub(super) fn query_packet_from_block(
        &self,
        request: &QueryPacketEventDataRequest,
        seqs: &[Sequence],
        block_height: &ICSHeight,
    ) -> Result<(Vec<IbcEventWithHeight>, Vec<IbcEventWithHeight>), Error> {
        use crate::chain::cosmos::query::tx::filter_matching_event;

        let mut begin_block_events = vec![];
        let mut end_block_events = vec![];

        let tm_height =
            tendermint::block::Height::try_from(block_height.revision_height()).unwrap();

        let response = self
            .block_on(self.sequencer_client.block_results(tm_height))
            .map_err(|e| Error::rpc(self.config.rpc_addr().clone(), e))?;

        let response_height = ICSHeight::new(self.id().version(), u64::from(response.height))
            .map_err(|_| Error::invalid_height_no_source())?;

        begin_block_events.append(
            &mut response
                .begin_block_events
                .unwrap_or_default()
                .iter()
                .filter_map(|ev| filter_matching_event(ev, request, seqs))
                .map(|ev| IbcEventWithHeight::new(ev, response_height))
                .collect(),
        );

        end_block_events.append(
            &mut response
                .end_block_events
                .unwrap_or_default()
                .iter()
                .filter_map(|ev| filter_matching_event(ev, request, seqs))
                .map(|ev| IbcEventWithHeight::new(ev, response_height))
                .collect(),
        );

        Ok((begin_block_events, end_block_events))
    }
}

impl ChainEndpoint for AstriaEndpoint {
    /// Type of light blocks for this chain
    type LightBlock = LightBlock;

    /// Type of headers for this chain
    type Header = Header;

    /// Type of consensus state for this chain
    type ConsensusState = TendermintConsensusState;

    /// Type of the client state for this chain
    type ClientState = TendermintClientState;

    /// The type of time for this chain
    type Time = TmTime;

    /// Type of the key pair used for signatures of messages on chain
    type SigningKeyPair = Ed25519KeyPair;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId {
        self.config.id()
    }

    /// Returns the chain configuration
    fn config(&self) -> ChainConfig {
        self.config.clone()
    }

    // Life cycle

    /// Constructs the chain
    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let keybase = KeyRing::new_ed25519(crate::keyring::Store::Test, "test", config.id(), &None)
            .map_err(|e| Error::other(e.into()))?;
        Self::new(config, keybase, rt)
    }

    /// Shutdown the chain runtime
    fn shutdown(self) -> Result<(), Error> {
        Ok(())
    }

    /// Perform a health check
    fn health_check(&mut self) -> Result<HealthCheck, Error> {
        Ok(HealthCheck::Healthy)
    }

    // Events
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

    // Keyring

    /// Returns the chain's keybase
    fn keybase(&self) -> &KeyRing<Self::SigningKeyPair> {
        &self.keybase
    }

    /// Returns the chain's keybase, mutably
    fn keybase_mut(&mut self) -> &mut KeyRing<Self::SigningKeyPair> {
        &mut self.keybase
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        use std::str::FromStr as _;

        use crate::keyring::SigningKeyPair as _;

        Signer::from_str(&self.get_key()?.account()).map_err(|e| Error::other(e.into()))
    }

    /// Get the signing key pair
    fn get_key(&self) -> Result<Self::SigningKeyPair, Error> {
        self.keybase
            .get_key(self.config.key_name())
            .map_err(|e| Error::key_not_found(self.config.key_name().to_string(), e))
    }

    // Versioning

    /// Return the version of the IBC protocol that this chain is running, if known.
    fn version_specs(&self) -> Result<Specs, Error> {
        todo!()
    }

    // Send transactions

    /// Sends one or more transactions with `msgs` to chain and
    /// synchronously wait for it to be committed.
    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let runtime = self.rt.clone();
        let msg_len = tracked_msgs.msgs.len();
        let resp = runtime.block_on(self.broadcast_messages(tracked_msgs))?;

        // `wait_for_block_commits` will append the events to this
        let mut resps = vec![response_to_tx_sync_result(self.id(), msg_len, resp)];

        runtime.block_on(wait_for_block_commits(
            self.config.id(),
            &self.sequencer_client,
            self.config.rpc_addr(),
            &DEFAULT_RPC_TIMEOUT,
            &mut resps,
        ))?;

        let events = resps
            .into_iter()
            .flat_map(|resp| resp.events)
            .collect::<Vec<_>>();

        Ok(events)
    }

    /// Sends one or more transactions with `msgs` to chain.
    /// Non-blocking alternative to `send_messages_and_wait_commit` interface.
    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<TxResponse>, Error> {
        let runtime = self.rt.clone();
        runtime
            .block_on(self.broadcast_messages(tracked_msgs))
            .map(|resp| vec![resp])
    }

    /// Fetch a header from the chain at the given height and verify it.
    fn verify_header(
        &mut self,
        trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        let status = self.chain_status()?;
        if status.sync_info.catching_up {
            return Err(Error::chain_not_caught_up(
                self.config.rpc_addr().to_string(),
                self.id().clone(),
            ));
        }

        let latest_timestamp = status.sync_info.latest_block_time;
        self.light_client
            .verify(trusted, target, client_state, latest_timestamp)
            .map(|v| v.target)
    }

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        let status = self.chain_status()?;
        if status.sync_info.catching_up {
            return Err(Error::chain_not_caught_up(
                self.config.rpc_addr().to_string(),
                self.id().clone(),
            ));
        }

        let latest_timestamp = status.sync_info.latest_block_time;
        self.light_client
            .detect_misbehaviour(update, client_state, latest_timestamp)
    }

    // Queries

    /// Query the balance of the given account for the given denom.
    /// If no account is given, behavior must be specified, e.g. retrieve it from configuration file.
    /// If no denom is given, behavior must be specified, e.g. retrieve the denom used to pay tx fees.
    fn query_balance(
        &self,
        _key_name: Option<&str>,
        denom: Option<&str>,
    ) -> Result<Balance, Error> {
        use astria_core::{
            crypto::VerificationKey,
            protocol::account::v1alpha1::AssetBalance,
        };
        use astria_sequencer_client::{
            Address,
            SequencerClientExt as _,
        };

        let signing_key: ed25519_consensus::SigningKey =
            (*self.get_key()?.signing_key().as_bytes()).into(); // TODO cache this
        let verification_key = VerificationKey::try_from(signing_key.verification_key().to_bytes())
            .map_err(|e| Error::other(e.into()))?;
        let address = Address::builder()
            .verification_key(&verification_key)
            .prefix("astria")
            .try_build()
            .map_err(|e| Error::other(e.into()))?;
        let balance = self
            .block_on(self.sequencer_client.get_latest_balance(address))
            .map_err(|e| Error::other(Box::new(e)))?;

        // TODO: set this via the config
        let denom = denom.unwrap_or("nria");

        let balance: Vec<AssetBalance> = balance
            .balances
            .into_iter()
            .filter(|b| b.denom.to_string() == denom)
            .collect();

        if balance.is_empty() {
            return Ok(Balance {
                amount: 0.to_string(),
                denom: denom.to_string(),
            });
        }

        Ok(Balance {
            amount: balance[0].balance.to_string(),
            denom: denom.to_string(),
        })
    }

    /// Query the balances of the given account for all the denom.
    /// If no account is given, behavior must be specified, e.g. retrieve it from configuration file.
    fn query_all_balances(&self, _key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        todo!()
    }

    /// Query the denomination trace given a trace hash.
    fn query_denom_trace(&self, _hash: String) -> Result<DenomTrace, Error> {
        todo!()
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        Ok(penumbra_ibc::IBC_SUBSTORE_PREFIX
            .as_bytes()
            .to_vec()
            .try_into()
            .unwrap())
    }

    /// Query the latest height and timestamp the application is at
    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        let rt = self.rt.clone();
        let head_block = rt
            .block_on(self.sequencer_client.latest_block())
            .map_err(|e| Error::rpc(self.config.rpc_addr().clone(), e))?;
        Ok(ChainStatus {
            height: ICSHeight::new(self.id().version(), head_block.block.header.height.value())
                .map_err(|e| Error::other(Box::new(e)))?,
            timestamp: head_block.block.header.time.into(),
        })
    }

    /// Performs a query to retrieve the state of all clients that a chain hosts.
    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        use crate::{
            chain::cosmos::client_id_suffix,
            util::pretty::PrettyIdentifiedClientState,
        };

        let mut client = self.ibc_client_grpc_client.clone();

        let request = tonic::Request::new(request.into());
        let response = self
            .block_on(client.client_states(request))
            .map_err(|e| Error::grpc_status(e, "query_clients".to_owned()))?
            .into_inner();

        // Deserialize into domain type
        let mut clients: Vec<IdentifiedAnyClientState> = response
            .client_states
            .into_iter()
            .filter_map(|cs| {
                IdentifiedAnyClientState::try_from(cs.clone())
                    .map_err(|e| {
                        warn!(
                            "failed to parse client state {}. Error: {}",
                            PrettyIdentifiedClientState(&cs),
                            e
                        )
                    })
                    .ok()
            })
            .collect();

        // Sort by client identifier counter
        clients.sort_by_cached_key(|c| client_id_suffix(&c.client_id).unwrap_or(0));

        Ok(clients)
    }

    /// Performs a query to retrieve the state of the specified light client. A
    /// proof can optionally be returned along with the result.
    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        let mut client = self.ibc_client_grpc_client.clone();

        let mut req = ibc_proto::ibc::core::client::v1::QueryClientStateRequest {
            client_id: request.client_id.to_string(),
            // TODO: height is ignored
        }
        .into_request();

        let map = req.metadata_mut();
        let height_str: String = match request.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };
        map.insert("height", height_str.parse().expect("valid ascii string"));

        let response = self
            .block_on(client.client_state(req))
            .map_err(|e| Error::grpc_status(e, "query_client_state".to_owned()))?
            .into_inner();

        let Some(client_state) = response.client_state else {
            return Err(Error::empty_response_value());
        };

        let client_state: AnyClientState = client_state
            .try_into()
            .map_err(|e| Error::other(Box::new(e)))?;

        match include_proof {
            IncludeProof::Yes => Ok((client_state, Some(decode_merkle_proof(response.proof)?))),
            IncludeProof::No => Ok((client_state, None)),
        }
    }

    /// Query the consensus state at the specified height for a given client.
    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        let mut client = self.ibc_client_grpc_client.clone();

        let mut req = ibc_proto::ibc::core::client::v1::QueryConsensusStateRequest {
            client_id: request.client_id.to_string(),
            revision_height: request.consensus_height.revision_height(),
            revision_number: request.consensus_height.revision_number(),
            latest_height: false, // TODO?
        }
        .into_request();

        let map = req.metadata_mut();
        let height_str: String = match request.query_height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };
        map.insert("height", height_str.parse().expect("valid ascii string"));

        let response = self
            .block_on(client.consensus_state(req))
            .map_err(|e| Error::grpc_status(e, "query_consensus_state".to_owned()))?
            .into_inner();

        let Some(consensus_state) = response.consensus_state else {
            return Err(Error::empty_response_value());
        };

        let consensus_state: AnyConsensusState = consensus_state
            .try_into()
            .map_err(|e| Error::other(Box::new(e)))?;

        if !matches!(consensus_state, AnyConsensusState::Tendermint(_)) {
            return Err(Error::consensus_state_type_mismatch(
                ClientType::Tendermint,
                consensus_state.client_type(),
            ));
        }

        match include_proof {
            IncludeProof::Yes => Ok((consensus_state, Some(decode_merkle_proof(response.proof)?))),
            IncludeProof::No => Ok((consensus_state, None)),
        }
    }

    /// Query the heights of every consensus state for a given client.
    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<ICSHeight>, Error> {
        let mut client = self.ibc_client_grpc_client.clone();

        let req = ibc_proto::ibc::core::client::v1::QueryConsensusStateHeightsRequest {
            client_id: request.client_id.to_string(),
            pagination: Default::default(),
        };

        let response = self
            .block_on(client.consensus_state_heights(req))
            .map_err(|e| Error::grpc_status(e, "query_consensus_state_heights".to_owned()))?
            .into_inner();

        let heights = response
            .consensus_state_heights
            .into_iter()
            .filter_map(|h| ICSHeight::new(h.revision_number, h.revision_height).ok())
            .collect();
        Ok(heights)
    }

    fn query_upgraded_client_state(
        &self,
        _request: QueryUpgradedClientStateRequest, // TODO: height ignored
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        let mut client = self.ibc_client_grpc_client.clone();
        let req = ibc_proto::ibc::core::client::v1::QueryUpgradedClientStateRequest {};

        let response = self
            .block_on(client.upgraded_client_state(req))
            .map_err(|e| Error::grpc_status(e, "query_upgraded_client_state".to_owned()))?
            .into_inner();

        let client_state = response
            .upgraded_client_state
            .ok_or_else(Error::empty_response_value)?;

        let _client_state: AnyClientState = client_state
            .try_into()
            .map_err(|e| Error::other(Box::new(e)))?;

        todo!()
    }

    fn query_upgraded_consensus_state(
        &self,
        _request: QueryUpgradedConsensusStateRequest, // TODO: height ignored
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        let mut client = self.ibc_client_grpc_client.clone();
        let req = ibc_proto::ibc::core::client::v1::QueryUpgradedConsensusStateRequest {};
        let response = self
            .block_on(client.upgraded_consensus_state(req))
            .map_err(|e| Error::grpc_status(e, "query_upgraded_consensus_state".to_owned()))?
            .into_inner();

        let consensus_state = response
            .upgraded_consensus_state
            .ok_or_else(Error::empty_response_value)?;

        let _consensus_state: AnyConsensusState = consensus_state
            .try_into()
            .map_err(|e| Error::other(Box::new(e)))?;

        todo!()
    }

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        use crate::util::pretty::PrettyIdentifiedConnection;

        let mut client = self.ibc_connection_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.connections(request))
            .map_err(|e| Error::grpc_status(e, "query_connections".to_owned()))?
            .into_inner();

        let connections = response
            .connections
            .into_iter()
            .filter_map(|co| {
                IdentifiedConnectionEnd::try_from(co.clone())
                    .map_err(|e| {
                        warn!(
                            "connection with ID {} failed parsing. Error: {}",
                            PrettyIdentifiedConnection(&co),
                            e
                        )
                    })
                    .ok()
            })
            .collect();

        Ok(connections)
    }

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        let connections = self.query_connections(QueryConnectionsRequest {
            pagination: Default::default(),
        })?;

        let mut client_conns = vec![];
        for connection in connections {
            if connection
                .connection_end
                .client_id_matches(&request.client_id)
            {
                client_conns.push(connection.connection_id);
            }
        }

        Ok(client_conns)
    }

    /// Performs a query to retrieve the connection associated with a given
    /// connection identifier. A proof can optionally be returned along with the
    /// result.
    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        let mut client = self.ibc_connection_grpc_client.clone();
        let mut req = ibc_proto::ibc::core::connection::v1::QueryConnectionRequest {
            connection_id: request.connection_id.to_string(),
            // TODO height is ignored
        }
        .into_request();

        let map = req.metadata_mut();
        let height_str: String = match request.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };
        map.insert("height", height_str.parse().expect("valid ascii string"));

        let response = self.block_on(client.connection(req)).map_err(|e| {
            if e.code() == tonic::Code::NotFound {
                Error::connection_not_found(request.connection_id.clone())
            } else {
                Error::grpc_status(e, "query_connection".to_owned())
            }
        })?;

        let resp = response.into_inner();
        let connection_end: ConnectionEnd = match resp.connection {
            Some(raw_connection) => raw_connection.try_into().map_err(Error::ics03)?,
            None => {
                // When no connection is found, the GRPC call itself should return
                // the NotFound error code. Nevertheless even if the call is successful,
                // the connection field may not be present, because in protobuf3
                // everything is optional.
                return Err(Error::connection_not_found(request.connection_id.clone()));
            }
        };

        match include_proof {
            IncludeProof::Yes => Ok((connection_end, Some(decode_merkle_proof(resp.proof)?))),
            IncludeProof::No => Ok((connection_end, None)),
        }
    }

    /// Performs a query to retrieve all channels associated with a connection.
    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        use crate::util::pretty::PrettyIdentifiedChannel;

        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.connection_channels(request))
            .map_err(|e| Error::grpc_status(e, "query_connection_channels".to_owned()))?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| {
                IdentifiedChannelEnd::try_from(ch.clone())
                    .map_err(|e| {
                        warn!(
                            "channel with ID {} failed parsing. Error: {}",
                            PrettyIdentifiedChannel(&ch),
                            e
                        )
                    })
                    .ok()
            })
            .collect();
        Ok(channels)
    }

    /// Performs a query to retrieve all the channels of a chain.
    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        use crate::util::pretty::PrettyIdentifiedChannel;

        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.channels(request))
            .map_err(|e| Error::grpc_status(e, "query_channels".to_owned()))?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| {
                IdentifiedChannelEnd::try_from(ch.clone())
                    .map_err(|e| {
                        warn!(
                            "channel with ID {} failed parsing. Error: {}",
                            PrettyIdentifiedChannel(&ch),
                            e
                        );
                    })
                    .ok()
            })
            .collect();

        Ok(channels)
    }

    /// Performs a query to retrieve the channel associated with a given channel
    /// identifier. A proof can optionally be returned along with the result.
    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let req = ibc_proto::ibc::core::channel::v1::QueryChannelRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
        };

        let request = tonic::Request::new(req);
        let response = self
            .block_on(client.channel(request))
            .map_err(|e| Error::grpc_status(e, "query_channel".to_owned()))?
            .into_inner();

        let Some(channel_end) = response.channel else {
            return Err(Error::empty_response_value());
        };

        let channel_end: ChannelEnd = channel_end
            .try_into()
            .map_err(|e| Error::other(Box::new(e)))?;

        match include_proof {
            IncludeProof::Yes => Ok((channel_end, Some(decode_merkle_proof(response.proof)?))),
            IncludeProof::No => Ok((channel_end, None)),
        }
    }

    /// Performs a query to retrieve the client state for the channel associated
    /// with a given channel identifier.
    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.channel_client_state(request))
            .map_err(|e| Error::grpc_status(e, "query_channel_client_state".to_owned()))?
            .into_inner();

        let client_state: Option<IdentifiedAnyClientState> = response
            .identified_client_state
            .map_or_else(|| None, |proto_cs| proto_cs.try_into().ok());

        Ok(client_state)
    }

    /// Performs a query to retrieve a stored packet commitment hash, stored on
    /// the chain at path `path::CommitmentsPath`. A proof can optionally be
    /// returned along with the result.
    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let req = ibc_proto::ibc::core::channel::v1::QueryPacketCommitmentRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            sequence: request.sequence.into(),
        };

        let request = tonic::Request::new(req);
        let response = self
            .block_on(client.packet_commitment(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_commitment".to_owned()))?
            .into_inner();

        match include_proof {
            IncludeProof::Yes => Ok((
                response.commitment,
                Some(decode_merkle_proof(response.proof)?),
            )),
            IncludeProof::No => Ok((response.commitment, None)),
        }
    }

    /// Performs a query to retrieve all the packet commitments hashes
    /// associated with a channel. Returns the corresponding packet sequence
    /// numbers and the height at which they were retrieved.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.packet_commitments(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_commitments".to_owned()))?
            .into_inner();

        let mut commitment_sequences: Vec<Sequence> = response
            .commitments
            .into_iter()
            .map(|v| v.sequence.into())
            .collect();
        commitment_sequences.sort_unstable();

        let height = response
            .height
            .and_then(|raw_height| raw_height.try_into().ok())
            .ok_or_else(|| Error::grpc_response_param("height".to_string()))?;

        Ok((commitment_sequences, height))
    }

    /// Performs a query to retrieve a given packet receipt, stored on the chain at path
    /// `path::CommitmentsPath`. A proof can optionally be returned along with the result.
    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let req = ibc_proto::ibc::core::channel::v1::QueryPacketReceiptRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            sequence: request.sequence.into(),
            // TODO: height is ignored
        };

        let request = tonic::Request::new(req);
        let response = self
            .block_on(client.packet_receipt(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_receipt".to_owned()))?
            .into_inner();

        // TODO: is this right?
        let value = match response.received {
            true => vec![1],
            false => vec![0],
        };

        match include_proof {
            IncludeProof::Yes => Ok((value, Some(decode_merkle_proof(response.proof)?))),
            IncludeProof::No => Ok((value, None)),
        }
    }

    /// Performs a query about which IBC packets in the specified list has not
    /// been received. Returns the sequence numbers of the packets that were not
    /// received.
    ///
    /// For example, given a request with the sequence numbers `[5,6,7,8]`, a
    /// response of `[7,8]` would indicate that packets 5 & 6 were received,
    /// while packets 7, 8 were not.
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();

        let request = tonic::Request::new(request.into());

        let mut response = self
            .block_on(client.unreceived_packets(request))
            .map_err(|e| Error::grpc_status(e, "query_unreceived_packets".to_owned()))?
            .into_inner();

        response.sequences.sort_unstable();
        Ok(response
            .sequences
            .into_iter()
            .map(|seq| seq.into())
            .collect())
    }

    /// Performs a query to retrieve a stored packet acknowledgement hash,
    /// stored on the chain at path `path::AcksPath`. A proof can optionally be
    /// returned along with the result.
    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let req = ibc_proto::ibc::core::channel::v1::QueryPacketAcknowledgementRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            sequence: request.sequence.into(),
            // TODO: height is ignored
        };

        let request = tonic::Request::new(req);
        let response = self
            .block_on(client.packet_acknowledgement(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_acknowledgement".to_owned()))?
            .into_inner();

        match include_proof {
            IncludeProof::Yes => Ok((
                response.acknowledgement,
                Some(decode_merkle_proof(response.proof)?),
            )),
            IncludeProof::No => Ok((response.acknowledgement, None)),
        }
    }

    /// Performs a query to retrieve all the packet acknowledgements associated
    /// with a channel. Returns the corresponding packet sequence numbers and
    /// the height at which they were retrieved.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.packet_acknowledgements(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_acknowledgements".to_owned()))?
            .into_inner();

        let acks_sequences = response
            .acknowledgements
            .into_iter()
            .map(|v| v.sequence.into())
            .collect();

        let height = response
            .height
            .and_then(|raw_height| raw_height.try_into().ok())
            .ok_or_else(|| Error::grpc_response_param("height".to_string()))?;

        Ok((acks_sequences, height))
    }

    /// Performs a query about which IBC packets in the specified list has not
    /// been acknowledged. Returns the sequence numbers of the packets that were not
    /// acknowledged.
    ///
    /// For example, given a request with the sequence numbers `[5,6,7,8]`, a
    /// response of `[7,8]` would indicate that packets 5 & 6 were acknowledged,
    /// while packets 7, 8 were not.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let mut response = self
            .block_on(client.unreceived_acks(request))
            .map_err(|e| Error::grpc_status(e, "query_unreceived_acknowledgements".to_owned()))?
            .into_inner();

        response.sequences.sort_unstable();
        Ok(response
            .sequences
            .into_iter()
            .map(|seq| seq.into())
            .collect())
    }

    /// Performs a query to retrieve `nextSequenceRecv` stored at path
    /// `path::SeqRecvsPath` as defined in ICS-4. A proof can optionally be
    /// returned along with the result.
    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.next_sequence_receive(request))
            .map_err(|e| Error::grpc_status(e, "query_next_sequence_receive".to_owned()))?
            .into_inner();

        match include_proof {
            IncludeProof::Yes => Ok((
                response.next_sequence_receive.into(),
                Some(decode_merkle_proof(response.proof)?),
            )),
            IncludeProof::No => Ok((response.next_sequence_receive.into(), None)),
        }
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        use crate::chain::cosmos::query::tx::query_txs;

        self.block_on(query_txs(
            self.id(),
            &self.sequencer_client,
            self.config.rpc_addr(),
            request,
        ))
    }

    fn query_packet_events(
        &self,
        mut request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        use crate::chain::cosmos::{
            query::tx::{
                query_packets_from_block,
                query_packets_from_txs,
            },
            sort_events_by_sequence,
        };

        match request.height {
            // Usage note: `Qualified::Equal` is currently only used in the call hierarchy involving
            // the CLI methods, namely the CLI for `tx packet-recv` and `tx packet-ack` when the
            // user passes the flag `packet-data-query-height`.
            Qualified::Equal(_) => self.block_on(query_packets_from_block(
                self.id(),
                &self.sequencer_client,
                self.config.rpc_addr(),
                &request,
            )),
            Qualified::SmallerEqual(_) => {
                let tx_events = self.block_on(query_packets_from_txs(
                    self.id(),
                    &self.sequencer_client,
                    self.config.rpc_addr(),
                    &request,
                ))?;

                let recvd_sequences: Vec<_> = tx_events
                    .iter()
                    .filter_map(|eh| eh.event.packet().map(|p| p.sequence))
                    .collect();

                request
                    .sequences
                    .retain(|seq| !recvd_sequences.contains(seq));

                let (start_block_events, end_block_events) = if !request.sequences.is_empty() {
                    self.block_on(self.query_packets_from_blocks(&request))?
                } else {
                    Default::default()
                };

                // Events should be ordered in the following fashion,
                // for any two blocks b1, b2 at height h1, h2 with h1 < h2:
                // b1.start_block_events
                // b1.tx_events
                // b1.end_block_events
                // b2.start_block_events
                // b2.tx_events
                // b2.end_block_events
                //
                // As of now, we just sort them by sequence number which should
                // yield a similar result and will revisit this approach in the future.
                let mut events = vec![];
                events.extend(start_block_events);
                events.extend(tx_events);
                events.extend(end_block_events);

                sort_events_by_sequence(&mut events);

                Ok(events)
            }
        }
    }

    fn query_host_consensus_state(
        &self,
        _request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        todo!()
    }

    fn build_client_state(
        &self,
        height: ICSHeight,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        use ibc_relayer_types::clients::ics07_tendermint::client_state::AllowUpdate;

        let ClientSettings::Tendermint(settings) = settings;

        // two hour duration
        // TODO what is this?
        let two_hours = Duration::from_secs(2 * 60 * 60);
        let unbonding_period = two_hours;
        let trusting_period_default = 2 * unbonding_period / 3;
        let trusting_period = settings.trusting_period.unwrap_or(trusting_period_default);

        let proof_specs = crate::chain::astria::proof_specs::proof_spec_with_prehash();

        Self::ClientState::new(
            self.id().clone(),
            settings.trust_threshold,
            trusting_period,
            unbonding_period,
            settings.max_clock_drift,
            height,
            proof_specs,
            vec!["upgrade".to_string(), "upgradedIBCState".to_string()],
            AllowUpdate {
                after_expiry: true,
                after_misbehaviour: true,
            },
        )
        .map_err(Error::ics07)
    }

    fn build_header(
        &mut self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        use crate::light_client::Verified;

        let now = self.chain_status()?.sync_info.latest_block_time;

        // Get the light block at target_height from chain.
        let Verified { target, supporting } = self.light_client.header_and_minimal_set(
            trusted_height,
            target_height,
            client_state,
            now,
        )?;

        Ok((target, supporting))
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        Ok(Self::ConsensusState::from(light_block.signed_header.header))
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        _channel_id: &ChannelId,
        _port_id: &PortId,
        _counterparty_payee: &Signer,
    ) -> Result<(), Error> {
        todo!()
    }

    fn cross_chain_query(
        &self,
        _requests: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error> {
        todo!()
    }

    fn query_incentivized_packet(
        &self,
        _request: QueryIncentivizedPacketRequest,
    ) -> Result<QueryIncentivizedPacketResponse, Error> {
        todo!()
    }

    fn query_consumer_chains(&self) -> Result<Vec<(ChainId, ClientId)>, Error> {
        todo!()
    }
}
