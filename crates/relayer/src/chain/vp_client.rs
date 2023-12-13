use super::client::ClientSettings;
use super::ic::VpClient;
use crate::keyring::{KeyRing, Secp256k1KeyPair};
use crate::{
    account::Balance,
    chain::endpoint::{ChainEndpoint, ChainStatus, HealthCheck},
    chain::handle::Subscription,
    chain::requests::{
        CrossChainQueryRequest, QueryChannelClientStateRequest, QueryChannelRequest,
        QueryChannelsRequest, QueryClientConnectionsRequest, QueryClientStatesRequest,
        QueryConnectionChannelsRequest, QueryConnectionRequest, QueryConnectionsRequest,
        QueryConsensusStateHeightsRequest, QueryConsensusStateRequest,
        QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
        QueryPacketCommitmentsRequest, QueryPacketEventDataRequest, QueryTxRequest,
        QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
    },
    chain::requests::{
        IncludeProof, QueryClientStateRequest, QueryHostConsensusStateRequest,
        QueryPacketAcknowledgementRequest, QueryPacketCommitmentRequest, QueryPacketReceiptRequest,
        QueryUpgradedClientStateRequest, QueryUpgradedConsensusStateRequest,
    },
    chain::tracking::TrackedMsgs,
    client_state::{AnyClientState, IdentifiedAnyClientState},
    config::ChainConfig,
    consensus_state::AnyConsensusState,
    denom::DenomTrace,
    error::Error,
    event::IbcEventWithHeight,
    misbehaviour::MisbehaviourEvidence,
};
use ic_agent::identity::Secp256k1Identity;
use ic_agent::Identity;

use alloc::{string::String, sync::Arc};
use core::future::Future;
use ibc_proto::Protobuf;
use ibc_relayer_types::clients::ics06_solomachine::consensus_state::PublicKey;
use ibc_relayer_types::clients::ics06_solomachine::{
    client_state::ClientState as SoloClientState,
    consensus_state::ConsensusState as SoloConsensusState, header::Header as SoloHeader,
};
use ibc_relayer_types::core::ics02_client::msgs::create_client::MsgCreateClient;
use ibc_relayer_types::{
    applications::ics31_icq::response::CrossChainQueryResponse,
    core::ics02_client::events::{Attributes, CreateClient, UpdateClient},
    core::ics23_commitment::commitment::CommitmentRoot,
    core::ics23_commitment::merkle::MerkleProof,
    core::{
        ics02_client::client_type::ClientType,
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics04_channel::{
            channel::{ChannelEnd, IdentifiedChannelEnd},
            packet::Sequence,
        },
        ics23_commitment::commitment::CommitmentPrefix,
        ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    },
    events::IbcEvent as IbcRelayerTypeEvent,
    signer::Signer,
    timestamp::Timestamp,
    Height, Height as ICSHeight,
};
use std::str::FromStr;

use prost::Message;
use semver::Version;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response as TxResponse;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::info;

/// Defines an upper limit on how large any transaction can be.
/// This upper limit is defined as a fraction relative to the block's
/// maximum bytes. For example, if the fraction is `0.9`, then
/// `max_tx_size` will not be allowed to exceed 0.9 of the
/// maximum block size of any Cosmos SDK network.
///
/// The default fraction we use is `0.9`; anything larger than that
/// would be risky, as transactions might be rejected; a smaller value
/// might be un-necessarily restrictive on the relayer side.
/// The [default max. block size in Tendermint 0.37 is 21MB](tm-37-max).
/// With a fraction of `0.9`, then Hermes will never permit the configuration
/// of `max_tx_size` to exceed ~18.9MB.
///
/// [tm-37-max]: https://github.com/tendermint/tendermint/blob/v0.37.0-rc1/types/params.go#L79
pub const BLOCK_MAX_BYTES_MAX_FRACTION: f64 = 0.9;
pub struct VpChain {
    config: ChainConfig,
    rt: Arc<TokioRuntime>,
    vp_client: VpClient,
    signer: String,
}

impl VpChain {
    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.rt.block_on(f)
    }
}

impl ChainEndpoint for VpChain {
    type LightBlock = ();
    type Header = SoloHeader;
    type ConsensusState = SoloConsensusState;
    type ClientState = SoloClientState;
    type Time = Timestamp;
    type SigningKeyPair = Secp256k1KeyPair;

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let canister_pem_path = if config.canister_pem.is_absolute() {
            config.canister_pem.clone()
        } else {
            let current_dir =
                std::env::current_dir().map_err(|e| Error::report_error(e.to_string()))?;
            current_dir.join(config.canister_pem.clone())
        };

        let signer = Secp256k1Identity::from_pem_file(canister_pem_path.clone()).map_err(|e| {
            let position = std::panic::Location::caller();
            Error::report_error(format!(
                "build vp client failed Error({:?}) \n{}",
                e, position
            ))
        })?;

        let sender = signer
            .sender()
            .map_err(|e| {
                let position = std::panic::Location::caller();
                Error::report_error(format!(
                    "build vp client failed Error({:?}) \n{}",
                    e, position
                ))
            })?
            .to_text();

        let vp_client = rt
            .block_on(VpClient::new(&config.ic_endpoint, &canister_pem_path))
            .map_err(|e| {
                let position = std::panic::Location::caller();
                Error::report_error(format!(
                    "build vp client failed Error({:?}) \n{}",
                    e, position
                ))
            })?;
        // Retrieve the version specification of this chain

        let chain = Self {
            config: config.clone(),
            vp_client,
            rt,
            signer: sender,
        };

        Ok(chain)
    }

    fn shutdown(self) -> Result<(), Error> {
        todo!()
    }

    fn keybase(&self) -> &KeyRing<Self::SigningKeyPair> {
        todo!()
    }

    fn keybase_mut(&mut self) -> &mut KeyRing<Self::SigningKeyPair> {
        todo!()
    }

    fn subscribe(&mut self) -> Result<Subscription, Error> {
        todo!()
    }

    /// Does multiple RPC calls to the full node, to check for
    /// reachability and some basic APIs are available.
    ///
    /// Currently this checks that:
    ///     - the node responds OK to `/health` RPC call;
    ///     - the node has transaction indexing enabled;
    ///     - the SDK & IBC versions are supported;
    ///
    /// Emits a log warning in case anything is amiss.
    /// Exits early if any health check fails, without doing any
    /// further checks.
    fn health_check(&mut self) -> Result<HealthCheck, Error> {
        todo!()
    }

    /// Fetch a header from the chain at the given height and verify it.
    fn verify_header(
        &mut self,
        _trusted: ICSHeight,
        _target: ICSHeight,
        _client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        Ok(())
    }

    /// Perform misbehavior detection for the given client state and update event.
    fn check_misbehaviour(
        &mut self,
        _update: &UpdateClient,
        _client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        todo!()
    }

    // Queries

    /// Send one or more transactions that include all the specified messages.
    /// The `proto_msgs` are split in transactions such they don't exceed the configured maximum
    /// number of messages per transaction and the maximum transaction size.
    /// Then `send_tx()` is called with each Tx. `send_tx()` determines the fee based on the
    /// on-chain simulation and if this exceeds the maximum gas specified in the configuration file
    /// then it returns error.
    /// TODO - more work is required here for a smarter split maybe iteratively accumulating/ evaluating
    /// msgs in a Tx until any of the max size, max num msgs, max fee are exceeded.
    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        info!(
            "tracked_msgs: {:?}, tracking_id: {:?}, \n{}",
            tracked_msgs
                .msgs
                .iter()
                .map(|msg| msg.type_url.clone())
                .collect::<Vec<_>>(),
            tracked_msgs.tracking_id,
            std::panic::Location::caller()
        );
        use ibc_proto::google::protobuf::Any;

        // let mut tracked_msgs = tracked_msgs.clone();
        // if tracked_msgs.tracking_id().to_string() != "ft-transfer" {
        let canister_id = self.config.canister_id.id.as_str();
        let mut msgs: Vec<Any> = Vec::new();
        for msg in tracked_msgs.messages() {
            let res = self
                .block_on(self.vp_client.deliver(canister_id, msg.encode_to_vec()))
                .map_err(|e| {
                    let position = std::panic::Location::caller();
                    Error::report_error(format!(
                        "call vp deliver failed Error({}) \n{}",
                        e, position
                    ))
                })?;
            assert!(!res.is_empty());
            if !res.is_empty() {
                msgs.push(Any::decode(&res[..]).map_err(|e| {
                    let position = std::panic::Location::caller();
                    Error::report_error(format!(
                        "decode call vp deliver result failed Error({}) \n{}",
                        e, position
                    ))
                })?);
            }
        }
        assert_eq!(msgs.len(), 1);
        let create_client_msg = msgs.remove(0);
        let domain_msg: MsgCreateClient = MsgCreateClient::decode_vec(&create_client_msg.value)
            .map_err(|e| {
                let position = std::panic::Location::caller();
                Error::report_error(format!(
                    "decode call vp deliver result failed Error({}) \n{}",
                    e, position
                ))
            })?;

        let client_state =
            ibc_relayer_types::clients::ics06_solomachine::client_state::ClientState::try_from(
                domain_msg.client_state,
            )
            .unwrap();
        println!("new solomachine client state created: {:?}", client_state);
        let serialized_pub_key =
            serde_json::to_string(&client_state.consensus_state.public_key.0).unwrap();
        println!("pubkey: {:?}", serialized_pub_key);
        println!(
            "timestamp: {:?}",
            client_state.consensus_state.timestamp.nanoseconds()
        );
        // todo: maybe need to check the response from ic
        let create_client_event = CreateClient::from(Attributes {
            client_id: ClientId::new(ClientType::Solomachine, 0).unwrap(),
            client_type: ClientType::Solomachine,
            consensus_height: ICSHeight::new(0, 1).unwrap(),
        });
        let create_event_with_height = IbcEventWithHeight {
            event: IbcRelayerTypeEvent::CreateClient(create_client_event),
            height: ICSHeight::new(0, 1).unwrap(),
        };
        Ok(vec![create_event_with_height])
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        _tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<TxResponse>, Error> {
        todo!()
    }

    /// Get the account for the signer
    fn get_signer(&self) -> Result<Signer, Error> {
        Signer::from_str(self.signer.as_str()).map_err(|e| Error::report_error(e.to_string()))
    }

    /// Get the chain configuration
    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn ibc_version(&self) -> Result<Option<Version>, Error> {
        todo!()
    }

    fn query_balance(
        &self,
        _key_name: Option<&str>,
        _denom: Option<&str>,
    ) -> Result<Balance, Error> {
        todo!()
    }

    fn query_all_balances(&self, _key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        todo!()
    }

    fn query_denom_trace(&self, _hash: String) -> Result<DenomTrace, Error> {
        todo!()
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        todo!()
    }

    /// Query the application status
    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        // Add template code here
        Ok(ChainStatus {
            height: ICSHeight::new(0, 1).unwrap(),
            timestamp: Timestamp::none(),
        })
    }

    fn query_clients(
        &self,
        _request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        todo!()
    }

    fn query_client_state(
        &self,
        _request: QueryClientStateRequest,
        _include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        todo!()
    }

    fn query_upgraded_client_state(
        &self,
        _request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        todo!()
    }

    fn query_upgraded_consensus_state(
        &self,
        _request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        todo!()
    }

    fn query_consensus_state_heights(
        &self,
        _request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<ICSHeight>, Error> {
        todo!()
    }

    fn query_consensus_state(
        &self,
        _request: QueryConsensusStateRequest,
        _include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        todo!()
    }

    fn query_client_connections(
        &self,
        _request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        todo!()
    }

    fn query_connections(
        &self,
        _request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        todo!()
    }

    fn query_connection(
        &self,
        _request: QueryConnectionRequest,
        _include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        todo!()
    }

    fn query_connection_channels(
        &self,
        _request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        todo!()
    }

    fn query_channels(
        &self,
        _request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        todo!()
    }

    fn query_channel(
        &self,
        _request: QueryChannelRequest,
        _include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        todo!()
    }

    fn query_channel_client_state(
        &self,
        _request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        todo!()
    }

    fn query_packet_commitment(
        &self,
        _request: QueryPacketCommitmentRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        todo!()
    }

    /// Queries the packet commitment hashes associated with a channel.
    fn query_packet_commitments(
        &self,
        _request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        todo!()
    }

    fn query_packet_receipt(
        &self,
        _request: QueryPacketReceiptRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        todo!()
    }

    /// Queries the unreceived packet sequences associated with a channel.
    fn query_unreceived_packets(
        &self,
        _request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        todo!()
    }

    fn query_packet_acknowledgement(
        &self,
        _request: QueryPacketAcknowledgementRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        todo!()
    }

    /// Queries the packet acknowledgment hashes associated with a channel.
    fn query_packet_acknowledgements(
        &self,
        _request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        todo!()
    }

    /// Queries the unreceived acknowledgements sequences associated with a channel.
    fn query_unreceived_acknowledgements(
        &self,
        _request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        todo!()
    }

    fn query_next_sequence_receive(
        &self,
        _request: QueryNextSequenceReceiveRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        todo!()
    }

    /// This function queries transactions for events matching certain criteria.
    /// 1. Client Update request - returns a vector with at most one update client event
    /// 2. Transaction event request - returns all IBC events resulted from a Tx execution
    fn query_txs(&self, _request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        todo!()
    }

    /// This function queries transactions for packet events matching certain criteria.
    /// It returns at most one packet event for each sequence specified in the request.
    ///    Note - there is no way to format the packet query such that it asks for Tx-es with either
    ///    sequence (the query conditions can only be AND-ed).
    ///    There is a possibility to include "<=" and ">=" conditions but it doesn't work with
    ///    string attributes (sequence is emmitted as a string).
    ///    Therefore, for packets we perform one tx_search for each sequence.
    ///    Alternatively, a single query for all packets could be performed but it would return all
    ///    packets ever sent.
    fn query_packet_events(
        &self,
        mut _request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        todo!()
    }

    fn query_host_consensus_state(
        &self,
        _request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        todo!()
    }

    fn build_client_state(
        &self,
        _height: ICSHeight,
        _settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        // todo: maybet this is not correct!
        let json_string = "{\"type\":\"tendermint/PubKeyEd25519\",\"value\":\"RblzMO4is5L1hZz6wo4kPbptzOyue6LTk4+lPhD1FRk=\"}";
        let pubkey: tendermint::PublicKey = serde_json::from_str(json_string).unwrap();

        let public_key = PublicKey::from(pubkey);
        let consensus_state = SoloConsensusState {
            public_key,
            diversifier: "oct".to_string(),
            timestamp: Timestamp::none(),
            root: CommitmentRoot::from(vec![1, 0, 1, 0]),
        };
        Ok(SoloClientState {
            sequence: Height::new(0, 1).unwrap(),
            is_frozen: false,
            consensus_state,
        })
    }

    fn build_consensus_state(
        &self,
        _light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        // todo: maybet this is not correct!
        let json_string = "{\"type\":\"tendermint/PubKeyEd25519\",\"value\":\"RblzMO4is5L1hZz6wo4kPbptzOyue6LTk4+lPhD1FRk=\"}";
        let pubkey: tendermint::PublicKey = serde_json::from_str(json_string).unwrap();

        let public_key = PublicKey::from(pubkey);
        let consensus_state = SoloConsensusState {
            public_key,
            diversifier: "oct".to_string(),
            timestamp: Timestamp::none(),
            root: CommitmentRoot::from(vec![1, 0, 1, 0]),
        };

        Ok(consensus_state)
    }

    fn build_header(
        &mut self,
        _trusted_height: ICSHeight,
        _target_height: ICSHeight,
        _client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        todo!()
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
        _request: ibc_proto::ibc::apps::fee::v1::QueryIncentivizedPacketRequest,
    ) -> Result<ibc_proto::ibc::apps::fee::v1::QueryIncentivizedPacketResponse, Error> {
        todo!()
    }

    fn query_consumer_chains(&self) -> Result<Vec<(ChainId, ClientId)>, Error> {
        todo!()
    }
}
