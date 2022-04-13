use core::fmt::Debug;

use crossbeam_channel as channel;
use serde::{Serialize, Serializer};

use ibc::{
    core::{
        ics02_client::client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight},
        ics02_client::client_state::{AnyClientState, IdentifiedAnyClientState},
        ics02_client::events::UpdateClient,
        ics02_client::header::AnyHeader,
        ics02_client::misbehaviour::MisbehaviourEvidence,
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics03_connection::version::Version,
        ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd},
        ics04_channel::packet::{PacketMsgType, Sequence},
        ics23_commitment::commitment::CommitmentPrefix,
        ics24_host::identifier::ChainId,
        ics24_host::identifier::ChannelId,
        ics24_host::identifier::{ClientId, ConnectionId, PortId},
    },
    events::IbcEvent,
    proofs::Proofs,
    query::{QueryBlockRequest, QueryTxRequest},
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

use crate::{
    chain::{client::ClientSettings, tx::TrackedMsgs, ChainStatus},
    config::ChainConfig,
    connection::ConnectionMsgType,
    error::Error,
    keyring::KeyEntry,
};

use super::{reply_channel, ChainHandle, ChainRequest, HealthCheck, ReplyTo, Subscription};

#[derive(Debug, Clone)]
pub struct BaseChainHandle {
    /// Chain identifier
    chain_id: ChainId,

    /// The handle's channel for sending requests to the runtime
    runtime_sender: channel::Sender<ChainRequest>,
}

impl BaseChainHandle {
    pub fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self {
        Self {
            chain_id,
            runtime_sender: sender,
        }
    }

    fn send<F, O>(&self, f: F) -> Result<O, Error>
    where
        F: FnOnce(ReplyTo<O>) -> ChainRequest,
        O: Debug,
    {
        let (sender, receiver) = reply_channel();
        let input = f(sender);

        self.runtime_sender.send(input).map_err(Error::send)?;

        receiver.recv().map_err(Error::channel_receive)?
    }
}

impl ChainHandle for BaseChainHandle {
    fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self {
        Self::new(chain_id, sender)
    }

    fn id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        self.send(|reply_to| ChainRequest::HealthCheck { reply_to })
    }

    fn shutdown(&self) -> Result<(), Error> {
        self.send(|reply_to| ChainRequest::Shutdown { reply_to })
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.send(|reply_to| ChainRequest::Subscribe { reply_to })
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
        self.send(|reply_to| ChainRequest::SendMessagesAndWaitCommit {
            tracked_msgs,
            reply_to,
        })
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        self.send(|reply_to| ChainRequest::SendMessagesAndWaitCheckTx {
            tracked_msgs,
            reply_to,
        })
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.send(|reply_to| ChainRequest::Signer { reply_to })
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        self.send(|reply_to| ChainRequest::Config { reply_to })
    }

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.send(|reply_to| ChainRequest::GetKey { reply_to })
    }

    fn add_key(&self, key_name: String, key: KeyEntry) -> Result<(), Error> {
        self.send(|reply_to| ChainRequest::AddKey {
            key_name,
            key,
            reply_to,
        })
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.send(|reply_to| ChainRequest::IbcVersion { reply_to })
    }

    fn query_status(&self) -> Result<ChainStatus, Error> {
        self.send(|reply_to| ChainRequest::QueryStatus { reply_to })
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.send(|reply_to| ChainRequest::QueryClients { request, reply_to })
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error> {
        self.send(|reply_to| ChainRequest::QueryClientState {
            client_id: client_id.clone(),
            height,
            reply_to,
        })
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.send(|reply_to| ChainRequest::QueryClientConnections { request, reply_to })
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.send(|reply_to| ChainRequest::QueryConsensusStates { request, reply_to })
    }

    fn query_consensus_state(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        query_height: Height,
    ) -> Result<AnyConsensusState, Error> {
        self.send(|reply_to| ChainRequest::QueryConsensusState {
            client_id,
            consensus_height,
            query_height,
            reply_to,
        })
    }

    fn query_upgraded_client_state(
        &self,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::QueryUpgradedClientState { height, reply_to })
    }

    fn query_upgraded_consensus_state(
        &self,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::QueryUpgradedConsensusState { height, reply_to })
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.send(|reply_to| ChainRequest::QueryCommitmentPrefix { reply_to })
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.send(|reply_to| ChainRequest::QueryCompatibleVersions { reply_to })
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error> {
        self.send(|reply_to| ChainRequest::QueryConnection {
            connection_id: connection_id.clone(),
            height,
            reply_to,
        })
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.send(|reply_to| ChainRequest::QueryConnections { request, reply_to })
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.send(|reply_to| ChainRequest::QueryConnectionChannels { request, reply_to })
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error> {
        self.send(|reply_to| ChainRequest::QueryNextSequenceReceive { request, reply_to })
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.send(|reply_to| ChainRequest::QueryChannels { request, reply_to })
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error> {
        self.send(|reply_to| ChainRequest::QueryChannel {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            height,
            reply_to,
        })
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.send(|reply_to| ChainRequest::QueryChannelClientState { request, reply_to })
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::ProvenClientState {
            client_id: client_id.clone(),
            height,
            reply_to,
        })
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::ProvenConnection {
            connection_id: connection_id.clone(),
            height,
            reply_to,
        })
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::ProvenClientConsensus {
            client_id: client_id.clone(),
            consensus_height,
            height,
            reply_to,
        })
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        self.send(|reply_to| ChainRequest::BuildHeader {
            trusted_height,
            target_height,
            client_state,
            reply_to,
        })
    }

    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<AnyClientState, Error> {
        self.send(|reply_to| ChainRequest::BuildClientState {
            height,
            settings,
            reply_to,
        })
    }

    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        self.send(|reply_to| ChainRequest::BuildConsensusState {
            trusted,
            target,
            client_state,
            reply_to,
        })
    }

    fn check_misbehaviour(
        &self,
        update_event: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.send(|reply_to| ChainRequest::BuildMisbehaviour {
            client_state,
            update_event,
            reply_to,
        })
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        self.send(
            |reply_to| ChainRequest::BuildConnectionProofsAndClientState {
                message_type,
                connection_id: connection_id.clone(),
                client_id: client_id.clone(),
                height,
                reply_to,
            },
        )
    }

    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<Proofs, Error> {
        self.send(|reply_to| ChainRequest::BuildChannelProofs {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            height,
            reply_to,
        })
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: Height,
    ) -> Result<(Vec<u8>, Proofs), Error> {
        self.send(|reply_to| ChainRequest::BuildPacketProofs {
            packet_type,
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
            height,
            reply_to,
        })
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketCommitments { request, reply_to })
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        self.send(|reply_to| ChainRequest::QueryUnreceivedPackets { request, reply_to })
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketAcknowledgement { request, reply_to })
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        self.send(|reply_to| ChainRequest::QueryUnreceivedAcknowledgement { request, reply_to })
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        self.send(|reply_to| ChainRequest::QueryPacketEventDataFromTxs { request, reply_to })
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketEventDataFromBlocks { request, reply_to })
    }

    fn query_host_consensus_state(&self, height: Height) -> Result<AnyConsensusState, Error> {
        self.send(|reply_to| ChainRequest::QueryHostConsensusState { height, reply_to })
    }
}

impl Serialize for BaseChainHandle {
    fn serialize<S>(&self, serializer: S) -> Result<<S as Serializer>::Ok, <S as Serializer>::Error>
    where
        S: Serializer,
    {
        self.id().serialize(serializer)
    }
}
