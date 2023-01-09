/*!
   Definition for a proxy [`ChainHandle`] implementation for tagged
   chain handles.

   Since we use the chain handle type to distinguish the chain tags, we will
   run into problem if we have the same concrete `ChainHandle` implementations
   for two chains that are not encapsulated behind an `impl ChainHandle`.

   This is the case for creating N-ary chains, because we cannot rely on the
   existential type encapsulation of `impl ChainHandle` to turn the
   [`CountingAndCachingChainHandle`](ibc_relayer::chain::handle::CountingAndCachingChainHandle) to turn
   them into unqiue types.

   A workaround for this is to add a unique tag to `CountingAndCachingChainHandle` itself,
   so that the type `MonoTagged<Tag, CountingAndCachingChainHandle>` becomes a unique chain
   handle type.

   We implement [`ChainHandle`] for a `MonoTagged<Tag, Handle>`, since if the
   underlying `Handle` type implements [`ChainHandle`], then a tagged handle
   is still a [`ChainHandle`].
*/

use crossbeam_channel as channel;
use tracing::Span;

use ibc_relayer::account::Balance;
use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::endpoint::{ChainStatus, HealthCheck};
use ibc_relayer::chain::handle::{ChainHandle, ChainRequest, Subscription};
use ibc_relayer::chain::requests::*;
use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::client_state::{AnyClientState, IdentifiedAnyClientState};
use ibc_relayer::config::ChainConfig;
use ibc_relayer::connection::ConnectionMsgType;
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer::denom::DenomTrace;
use ibc_relayer::error::Error;
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer::light_client::AnyHeader;
use ibc_relayer::misbehaviour::MisbehaviourEvidence;
use ibc_relayer_types::applications::ics31_icq::response::CrossChainQueryResponse;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics04_channel::channel::ChannelEnd;
use ibc_relayer_types::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc_relayer_types::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::core::ics24_host::identifier::ChannelId;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId, PortId};
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;

use crate::types::tagged::*;

/**
   Implement `ChainHandle` for any existential type `Handle: ChainHandle`.
   This allows us to tag values for chains that are tagged by position
   in [N-ary chains](crate::types::nary).
*/
impl<Tag, Handle> ChainHandle for MonoTagged<Tag, Handle>
where
    Tag: Send + Sync + 'static,
    Handle: ChainHandle,
{
    fn new(chain_id: ChainId, sender: channel::Sender<(Span, ChainRequest)>) -> Self {
        Self::new(Handle::new(chain_id, sender))
    }

    fn id(&self) -> ChainId {
        self.value().id()
    }

    fn shutdown(&self) -> Result<(), Error> {
        self.value().shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        self.value().health_check()
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.value().subscribe()
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.value().send_messages_and_wait_commit(tracked_msgs)
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        self.value().send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.value().get_signer()
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        self.value().config()
    }

    fn get_key(&self) -> Result<AnySigningKeyPair, Error> {
        self.value().get_key()
    }

    fn add_key(&self, key_name: String, key: AnySigningKeyPair) -> Result<(), Error> {
        self.value().add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.value().ibc_version()
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        self.value().query_application_status()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        self.value().query_latest_height()
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.value().query_clients(request)
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        self.value().query_client_state(request, include_proof)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.value().query_client_connections(request)
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<Height>, Error> {
        self.value().query_consensus_state_heights(request)
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        self.value().query_consensus_state(request, include_proof)
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.value().query_upgraded_client_state(request)
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.value().query_upgraded_consensus_state(request)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.value().query_commitment_prefix()
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.value().query_compatible_versions()
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        self.value().query_connection(request, include_proof)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.value().query_connections(request)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.value().query_connection_channels(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        self.value()
            .query_next_sequence_receive(request, include_proof)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.value().query_channels(request)
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        self.value().query_channel(request, include_proof)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.value().query_channel_client_state(request)
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        self.value()
            .build_header(trusted_height, target_height, client_state)
    }

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<AnyClientState, Error> {
        self.value().build_client_state(height, settings)
    }

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        self.value()
            .build_consensus_state(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &self,
        update: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.value().check_misbehaviour(update, client_state)
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        self.value().build_connection_proofs_and_client_state(
            message_type,
            connection_id,
            client_id,
            height,
        )
    }

    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<Proofs, Error> {
        self.value()
            .build_channel_proofs(port_id, channel_id, height)
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: Height,
    ) -> Result<Proofs, Error> {
        self.value()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.value().query_packet_commitment(request, include_proof)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.value().query_packet_commitments(request)
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.value().query_packet_receipt(request, include_proof)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.value().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.value()
            .query_packet_acknowledgement(request, include_proof)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.value().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.value().query_unreceived_acknowledgements(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.value().query_txs(request)
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.value().query_packet_events(request)
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error> {
        self.value().query_host_consensus_state(request)
    }

    fn query_balance(
        &self,
        key_name: Option<String>,
        denom: Option<String>,
    ) -> Result<Balance, Error> {
        self.value().query_balance(key_name, denom)
    }

    fn query_all_balances(&self, key_name: Option<String>) -> Result<Vec<Balance>, Error> {
        self.value().query_all_balances(key_name)
    }

    fn maybe_register_counterparty_payee(
        &self,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
    ) -> Result<(), Error> {
        self.value()
            .maybe_register_counterparty_payee(channel_id, port_id, counterparty_payee)
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        self.value().query_denom_trace(hash)
    }

    fn cross_chain_query(
        &self,
        request: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error> {
        self.value().cross_chain_query(request)
    }
}
