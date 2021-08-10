use std::fmt::Debug;

use crossbeam_channel as channel;
use serde::{Serialize, Serializer};

use ibc::ics02_client::client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight};
use ibc::ics02_client::client_state::{
    AnyClientState, IdentifiedAnyClientState, TaggedClientState,
};
use ibc::ics02_client::events::TaggedUpdateClient;
use ibc::ics02_client::misbehaviour::MisbehaviourEvidence;
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::query::QueryTxRequest;
use ibc::tagged::Tagged;
use ibc::{
    events::IbcEvent,
    ics02_client::header::AnyHeader,
    ics03_connection::version::Version,
    ics23_commitment::commitment::CommitmentPrefix,
    ics24_host::identifier::ChainId,
    ics24_host::identifier::ChannelId,
    ics24_host::identifier::{ClientId, ConnectionId, PortId},
    proofs::Proofs,
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

use crate::channel::{ChannelEnd, IdentifiedChannelEnd};
use crate::connection::{ConnectionEnd, ConnectionMsgType, IdentifiedConnectionEnd};
use crate::error::Error;
use crate::keyring::KeyEntry;

use super::{reply_channel, ChainHandle, ChainRequest, ReplyTo, Subscription};

#[derive(Debug, Clone)]
pub struct ProdChainHandle {
    /// Chain identifier
    chain_id: ChainId,

    /// The handle's channel for sending requests to the runtime
    runtime_sender: channel::Sender<ChainRequest>,
}

impl ProdChainHandle {
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

impl<Counterparty> ChainHandle<Counterparty> for ProdChainHandle {
    fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self {
        Self::new(chain_id, sender)
    }

    fn id(&self) -> Tagged<Self, ChainId> {
        Tagged::new(self.chain_id.clone())
    }

    fn shutdown(&self) -> Result<(), Error> {
        self.send(|reply_to| ChainRequest::Shutdown { reply_to })
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.send(|reply_to| ChainRequest::Subscribe { reply_to })
    }

    fn send_msgs(
        &self,
        proto_msgs: Vec<Tagged<Self, prost_types::Any>>,
    ) -> Result<Tagged<Self, Vec<IbcEvent>>, Error> {
        let proto_msgs = proto_msgs.into_iter().map(Tagged::untag).collect();
        let events = self.send(|reply_to| ChainRequest::SendMsgs {
            proto_msgs,
            reply_to,
        })?;

        Ok(Tagged::new(events))
    }

    fn get_signer(&self) -> Result<Tagged<Self, Signer>, Error> {
        let signer = self.send(|reply_to| ChainRequest::Signer { reply_to })?;

        Ok(Tagged::new(signer))
    }

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.send(|reply_to| ChainRequest::Key { reply_to })
    }

    fn module_version(&self, port_id: Tagged<Self, PortId>) -> Result<String, Error> {
        self.send(|reply_to| ChainRequest::ModuleVersion {
            port_id: port_id.untag(),
            reply_to,
        })
    }

    fn query_latest_height(&self) -> Result<Tagged<Self, Height>, Error> {
        let height = self.send(|reply_to| ChainRequest::QueryLatestHeight { reply_to })?;
        Ok(Tagged::new(height))
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<Tagged<Self, IdentifiedAnyClientState>>, Error> {
        let states = self.send(|reply_to| ChainRequest::QueryClients { request, reply_to })?;

        Ok(states.into_iter().map(Tagged::new).collect())
    }

    fn query_client_state(
        &self,
        client_id: Tagged<Self, ClientId>,
        height: Tagged<Self, Height>,
    ) -> Result<TaggedClientState<Self, Counterparty>, Error> {
        let state = self.send(|reply_to| ChainRequest::QueryClientState {
            client_id: client_id.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok(TaggedClientState::tag(state))
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<Tagged<Self, ConnectionId>>, Error> {
        let connection_ids =
            self.send(|reply_to| ChainRequest::QueryClientConnections { request, reply_to })?;

        Ok(connection_ids.into_iter().map(Tagged::new).collect())
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.send(|reply_to| ChainRequest::QueryConsensusStates { request, reply_to })
    }

    fn query_consensus_state(
        &self,
        client_id: Tagged<Self, ClientId>,
        consensus_height: Tagged<Counterparty, Height>,
        query_height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, AnyConsensusState>, Error> {
        let state = self.send(|reply_to| ChainRequest::QueryConsensusState {
            client_id: client_id.untag(),
            consensus_height: consensus_height.untag(),
            query_height: query_height.untag(),
            reply_to,
        })?;

        Ok(Tagged::new(state))
    }

    fn query_upgraded_client_state(
        &self,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyClientState>, Tagged<Self, MerkleProof>), Error> {
        let (state, proof) = self.send(|reply_to| ChainRequest::QueryUpgradedClientState {
            height: height.untag(),
            reply_to,
        })?;

        Ok((Tagged::new(state), Tagged::new(proof)))
    }

    fn query_upgraded_consensus_state(
        &self,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyConsensusState>, Tagged<Self, MerkleProof>), Error> {
        let (state, proof) = self.send(|reply_to| ChainRequest::QueryUpgradedConsensusState {
            height: height.untag(),
            reply_to,
        })?;

        Ok((Tagged::new(state), Tagged::new(proof)))
    }

    fn query_commitment_prefix(&self) -> Result<Tagged<Self, CommitmentPrefix>, Error> {
        let prefix = self.send(|reply_to| ChainRequest::QueryCommitmentPrefix { reply_to })?;

        Ok(Tagged::new(prefix))
    }

    fn query_compatible_versions(&self) -> Result<Vec<Tagged<Self, Version>>, Error> {
        let versions = self.send(|reply_to| ChainRequest::QueryCompatibleVersions { reply_to })?;

        Ok(versions.into_iter().map(Tagged::new).collect())
    }

    fn query_connection(
        &self,
        connection_id: Tagged<Self, ConnectionId>,
        height: Tagged<Self, Height>,
    ) -> Result<ConnectionEnd<Self, Counterparty>, Error> {
        let connection_end = self.send(|reply_to| ChainRequest::QueryConnection {
            connection_id: connection_id.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok(ConnectionEnd::tag(connection_end))
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd<Self, Counterparty>>, Error> {
        let connection_ends =
            self.send(|reply_to| ChainRequest::QueryConnections { request, reply_to })?;

        let tagged = connection_ends
            .into_iter()
            .map(IdentifiedConnectionEnd::tag)
            .collect();

        Ok(tagged)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd<Self, Counterparty>>, Error> {
        let channel_ends =
            self.send(|reply_to| ChainRequest::QueryConnectionChannels { request, reply_to })?;

        Ok(channel_ends
            .into_iter()
            .map(IdentifiedChannelEnd::tag)
            .collect())
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Tagged<Self, Sequence>, Error> {
        let sequence =
            self.send(|reply_to| ChainRequest::QueryNextSequenceReceive { request, reply_to })?;

        Ok(Tagged::new(sequence))
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd<Self, Counterparty>>, Error> {
        let channel_ends =
            self.send(|reply_to| ChainRequest::QueryChannels { request, reply_to })?;

        Ok(channel_ends
            .into_iter()
            .map(IdentifiedChannelEnd::tag)
            .collect())
    }

    fn query_channel(
        &self,
        port_id: Tagged<Self, PortId>,
        channel_id: Tagged<Self, ChannelId>,
        height: Tagged<Self, Height>,
    ) -> Result<ChannelEnd<Self, Counterparty>, Error> {
        let channel_end = self.send(|reply_to| ChainRequest::QueryChannel {
            port_id: port_id.untag(),
            channel_id: channel_id.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok(ChannelEnd::tag(channel_end))
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<Tagged<Self, IdentifiedAnyClientState>>, Error> {
        let m_state =
            self.send(|reply_to| ChainRequest::QueryChannelClientState { request, reply_to })?;

        Ok(m_state.map(Tagged::new))
    }

    fn proven_client_state(
        &self,
        client_id: Tagged<Self, ClientId>,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyClientState>, MerkleProof), Error> {
        let (state, proof) = self.send(|reply_to| ChainRequest::ProvenClientState {
            client_id: client_id.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok((Tagged::new(state), proof))
    }

    fn proven_connection(
        &self,
        connection_id: Tagged<Self, ConnectionId>,
        height: Tagged<Self, Height>,
    ) -> Result<(ConnectionEnd<Self, Counterparty>, MerkleProof), Error> {
        let (connection_end, proof) = self.send(|reply_to| ChainRequest::ProvenConnection {
            connection_id: connection_id.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok((ConnectionEnd::tag(connection_end), proof))
    }

    fn proven_client_consensus(
        &self,
        client_id: Tagged<Self, ClientId>,
        consensus_height: Tagged<Self, Height>,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyConsensusState>, MerkleProof), Error> {
        let (state, proof) = self.send(|reply_to| ChainRequest::ProvenClientConsensus {
            client_id: client_id.untag(),
            consensus_height: consensus_height.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok((Tagged::new(state), proof))
    }

    fn build_header(
        &self,
        trusted_height: Tagged<Self, Height>,
        target_height: Tagged<Self, Height>,
        client_state: TaggedClientState<Counterparty, Self>,
    ) -> Result<
        (
            Tagged<Counterparty, AnyHeader>,
            Vec<Tagged<Counterparty, AnyHeader>>,
        ),
        Error,
    > {
        let (header, headers) = self.send(|reply_to| ChainRequest::BuildHeader {
            trusted_height: trusted_height.untag(),
            target_height: target_height.untag(),
            client_state: client_state.0.untag(),
            reply_to,
        })?;

        Ok((
            Tagged::new(header),
            headers.into_iter().map(Tagged::new).collect(),
        ))
    }

    fn build_client_state(
        &self,
        height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, AnyClientState>, Error> {
        let state = self.send(|reply_to| ChainRequest::BuildClientState {
            height: height.untag(),
            reply_to,
        })?;

        Ok(Tagged::new(state))
    }

    fn build_consensus_state(
        &self,
        trusted: Tagged<Self, Height>,
        target: Tagged<Self, Height>,
        client_state: Tagged<Self, AnyClientState>,
    ) -> Result<Tagged<Self, AnyConsensusState>, Error> {
        let state = self.send(|reply_to| ChainRequest::BuildConsensusState {
            trusted: trusted.untag(),
            target: target.untag(),
            client_state: client_state.untag(),
            reply_to,
        })?;

        Ok(Tagged::new(state))
    }

    fn check_misbehaviour(
        &self,
        update_event: TaggedUpdateClient<Counterparty, Self>,
        client_state: TaggedClientState<Counterparty, Self>,
    ) -> Result<Option<Tagged<Counterparty, MisbehaviourEvidence>>, Error> {
        let res = self.send(|reply_to| ChainRequest::BuildMisbehaviour {
            client_state: client_state.0.untag(),
            update_event: update_event.untag(),
            reply_to,
        })?;

        Ok(res.map(Tagged::new))
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: Tagged<Self, ConnectionId>,
        client_id: Tagged<Self, ClientId>,
        height: Tagged<Self, Height>,
    ) -> Result<
        (
            Option<TaggedClientState<Self, Counterparty>>,
            Tagged<Self, Proofs>,
        ),
        Error,
    > {
        let (m_state, proof) =
            self.send(
                |reply_to| ChainRequest::BuildConnectionProofsAndClientState {
                    message_type,
                    connection_id: connection_id.untag(),
                    client_id: client_id.untag(),
                    height: height.untag(),
                    reply_to,
                },
            )?;

        Ok((m_state.map(TaggedClientState::tag), Tagged::new(proof)))
    }

    fn build_channel_proofs(
        &self,
        port_id: Tagged<Self, PortId>,
        channel_id: Tagged<Self, ChannelId>,
        height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, Proofs>, Error> {
        let proofs = self.send(|reply_to| ChainRequest::BuildChannelProofs {
            port_id: port_id.untag(),
            channel_id: channel_id.untag(),
            height: height.untag(),
            reply_to,
        })?;

        Ok(Tagged::new(proofs))
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: Tagged<Self, PortId>,
        channel_id: Tagged<Self, ChannelId>,
        sequence: Tagged<Self, Sequence>,
        height: Tagged<Self, Height>,
    ) -> Result<(Vec<u8>, Proofs), Error> {
        self.send(|reply_to| ChainRequest::BuildPacketProofs {
            packet_type,
            port_id: port_id.untag(),
            channel_id: channel_id.untag(),
            sequence: sequence.untag(),
            height: height.untag(),
            reply_to,
        })
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Tagged<Self, Height>), Error> {
        let (states, height) =
            self.send(|reply_to| ChainRequest::QueryPacketCommitments { request, reply_to })?;

        Ok((states, Tagged::new(height)))
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
    ) -> Result<(Vec<PacketState>, Tagged<Self, Height>), Error> {
        let (states, height) =
            self.send(|reply_to| ChainRequest::QueryPacketAcknowledgement { request, reply_to })?;

        Ok((states, Tagged::new(height)))
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        self.send(|reply_to| ChainRequest::QueryUnreceivedAcknowledgement { request, reply_to })
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        self.send(|reply_to| ChainRequest::QueryPacketEventData { request, reply_to })
    }
}

impl Serialize for ProdChainHandle {
    fn serialize<S>(&self, serializer: S) -> Result<<S as Serializer>::Ok, <S as Serializer>::Error>
    where
        S: Serializer,
    {
        self.chain_id.serialize(serializer)
    }
}
