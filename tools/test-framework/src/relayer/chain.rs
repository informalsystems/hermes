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
use ibc::core::ics02_client::client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight};
use ibc::core::ics02_client::client_state::{AnyClientState, IdentifiedAnyClientState};
use ibc::core::ics02_client::events::UpdateClient;
use ibc::core::ics02_client::misbehaviour::MisbehaviourEvidence;
use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::query::QueryTxRequest;
use ibc::{
    core::ics02_client::header::AnyHeader,
    core::ics03_connection::connection::ConnectionEnd,
    core::ics03_connection::version::Version,
    core::ics04_channel::channel::ChannelEnd,
    core::ics23_commitment::commitment::CommitmentPrefix,
    core::ics24_host::identifier::ChainId,
    core::ics24_host::identifier::ChannelId,
    core::ics24_host::identifier::{ClientId, ConnectionId, PortId},
    events::IbcEvent,
    proofs::Proofs,
    query::QueryBlockRequest,
    signer::Signer,
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryChannelClientStateRequest, QueryChannelsRequest,
    QueryConnectionChannelsRequest, QueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest,
    QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::{QueryClientStatesRequest, QueryConsensusStatesRequest};
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::ibc::core::connection::v1::QueryClientConnectionsRequest;
use ibc_proto::ibc::core::connection::v1::QueryConnectionsRequest;
use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::handle::{ChainHandle, ChainRequest, Subscription};
use ibc_relayer::chain::tx::TrackedMsgs;
use ibc_relayer::chain::{ChainStatus, HealthCheck};
use ibc_relayer::config::ChainConfig;
use ibc_relayer::error::Error;
use ibc_relayer::{connection::ConnectionMsgType, keyring::KeyEntry};

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
    fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self {
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
    ) -> Result<Vec<IbcEvent>, Error> {
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

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.value().get_key()
    }

    fn add_key(&self, key_name: String, key: KeyEntry) -> Result<(), Error> {
        self.value().add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.value().ibc_version()
    }

    fn query_status(&self) -> Result<ChainStatus, Error> {
        self.value().query_status()
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
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error> {
        self.value().query_client_state(client_id, height)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.value().query_client_connections(request)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.value().query_consensus_states(request)
    }

    fn query_consensus_state(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        query_height: Height,
    ) -> Result<AnyConsensusState, Error> {
        self.value()
            .query_consensus_state(client_id, consensus_height, query_height)
    }

    fn query_upgraded_client_state(
        &self,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.value().query_upgraded_client_state(height)
    }

    fn query_upgraded_consensus_state(
        &self,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.value().query_upgraded_consensus_state(height)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.value().query_commitment_prefix()
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.value().query_compatible_versions()
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error> {
        self.value().query_connection(connection_id, height)
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
    ) -> Result<Sequence, Error> {
        self.value().query_next_sequence_receive(request)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.value().query_channels(request)
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error> {
        self.value().query_channel(port_id, channel_id, height)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.value().query_channel_client_state(request)
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.value().proven_client_state(client_id, height)
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        self.value().proven_connection(connection_id, height)
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.value()
            .proven_client_consensus(client_id, consensus_height, height)
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
    ) -> Result<(Vec<u8>, Proofs), Error> {
        self.value()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.value().query_packet_commitments(request)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        self.value().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.value().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        self.value().query_unreceived_acknowledgement(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        self.value().query_txs(request)
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        self.value().query_blocks(request)
    }

    fn query_host_consensus_state(&self, height: Height) -> Result<AnyConsensusState, Error> {
        self.value().query_host_consensus_state(height)
    }
}
