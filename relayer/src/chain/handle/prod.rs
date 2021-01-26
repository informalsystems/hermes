use std::fmt::Debug;

use crossbeam_channel as channel;

use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};

use ibc::{
    events::IBCEvent,
    ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader},
    ics03_connection::connection::ConnectionEnd,
    ics03_connection::version::Version,
    ics04_channel::channel::{ChannelEnd, QueryPacketEventDataRequest},
    ics23_commitment::commitment::CommitmentPrefix,
    ics24_host::identifier::ChainId,
    ics24_host::identifier::ChannelId,
    ics24_host::identifier::{ClientId, ConnectionId, PortId},
    proofs::Proofs,
    Height,
};
use ibc_proto::ibc::core::commitment::v1::MerkleProof;

// FIXME: the handle should not depend on tendermint-specific types
use tendermint::account::Id as AccountId;

use super::{reply_channel, ChainHandle, ChainRequest, ReplyTo, Subscription};

use crate::{
    chain::QueryResponse,
    connection::ConnectionMsgType,
    error::{Error, Kind},
    keyring::store::KeyEntry,
};
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};

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

        self.runtime_sender
            .send(input)
            .map_err(|e| Kind::Channel.context(e))?;

        receiver.recv().map_err(|e| Kind::Channel.context(e))?
    }
}

impl ChainHandle for ProdChainHandle {
    fn id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn query(
        &self,
        path: ibc::ics24_host::Path,
        height: Height,
        prove: bool,
    ) -> Result<QueryResponse, Error> {
        self.send(|reply_to| ChainRequest::Query {
            path,
            height,
            prove,
            reply_to,
        })
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.send(|reply_to| ChainRequest::Subscribe { reply_to })
    }

    fn send_msgs(&self, proto_msgs: Vec<prost_types::Any>) -> Result<Vec<IBCEvent>, Error> {
        self.send(|reply_to| ChainRequest::SendMsgs {
            proto_msgs,
            reply_to,
        })
    }

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, Error> {
        self.send(|reply_to| ChainRequest::GetMinimalSet { from, to, reply_to })
    }

    fn get_signer(&self) -> Result<AccountId, Error> {
        self.send(|reply_to| ChainRequest::Signer { reply_to })
    }

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.send(|reply_to| ChainRequest::Key { reply_to })
    }

    fn module_version(&self, port_id: &PortId) -> Result<String, Error> {
        self.send(|reply_to| ChainRequest::ModuleVersion {
            port_id: port_id.clone(),
            reply_to,
        })
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        self.send(|reply_to| ChainRequest::QueryLatestHeight { reply_to })
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

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error> {
        self.send(|reply_to| ChainRequest::QueryChannel {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            height,
            reply_to,
        })
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
    ) -> Result<AnyHeader, Error> {
        self.send(|reply_to| ChainRequest::BuildHeader {
            trusted_height,
            target_height,
            reply_to,
        })
    }

    fn build_client_state(&self, height: Height) -> Result<AnyClientState, Error> {
        self.send(|reply_to| ChainRequest::BuildClientState { height, reply_to })
    }

    fn build_consensus_state(&self, height: Height) -> Result<AnyConsensusState, Error> {
        self.send(|reply_to| ChainRequest::BuildConsensusState { height, reply_to })
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
            channel_id: channel_id.clone(),
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
            channel_id: channel_id.clone(),
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

    fn query_txs(&self, request: QueryPacketEventDataRequest) -> Result<Vec<IBCEvent>, Error> {
        self.send(|reply_to| ChainRequest::QueryPacketEventData { request, reply_to })
    }
}
