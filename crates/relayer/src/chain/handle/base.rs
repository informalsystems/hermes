use core::fmt::{Debug, Display, Error as FmtError, Formatter};

use crossbeam_channel as channel;
use tracing::Span;

use ibc_relayer_types::{
    applications::ics31_icq::response::CrossChainQueryResponse,
    core::{
        ics02_client::events::UpdateClient,
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics03_connection::version::Version,
        ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd},
        ics04_channel::packet::{PacketMsgType, Sequence},
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::ChainId,
        ics24_host::identifier::ChannelId,
        ics24_host::identifier::{ClientId, ConnectionId, PortId},
    },
    proofs::Proofs,
    signer::Signer,
    Height,
};

use crate::{
    account::Balance,
    chain::{client::ClientSettings, endpoint::ChainStatus, requests::*, tracking::TrackedMsgs},
    client_state::{AnyClientState, IdentifiedAnyClientState},
    config::ChainConfig,
    connection::ConnectionMsgType,
    consensus_state::AnyConsensusState,
    denom::DenomTrace,
    error::Error,
    event::IbcEventWithHeight,
    keyring::AnySigningKeyPair,
    light_client::AnyHeader,
    misbehaviour::MisbehaviourEvidence,
};

use super::{reply_channel, ChainHandle, ChainRequest, HealthCheck, ReplyTo, Subscription};

/// A basic chain handle implementation.
/// For use in interactive CLIs, e.g., `query`, `tx`, etc.
#[derive(Debug, Clone)]
pub struct BaseChainHandle {
    /// Chain identifier
    chain_id: ChainId,

    /// The handle's channel for sending requests to the runtime
    runtime_sender: channel::Sender<(Span, ChainRequest)>,
}

impl BaseChainHandle {
    pub fn new(chain_id: ChainId, sender: channel::Sender<(Span, ChainRequest)>) -> Self {
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

        let span = Span::current();
        let input = f(sender);

        self.runtime_sender
            .send((span, input))
            .map_err(Error::send)?;

        receiver.recv().map_err(Error::channel_receive)?
    }
}

impl Display for BaseChainHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "BaseChainHandle {{ chain_id: {} }}", self.chain_id)
    }
}

impl ChainHandle for BaseChainHandle {
    fn new(chain_id: ChainId, sender: channel::Sender<(Span, ChainRequest)>) -> Self {
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
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
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

    fn get_key(&self) -> Result<AnySigningKeyPair, Error> {
        self.send(|reply_to| ChainRequest::GetKey { reply_to })
    }

    fn add_key(&self, key_name: String, key: AnySigningKeyPair) -> Result<(), Error> {
        self.send(|reply_to| ChainRequest::AddKey {
            key_name,
            key,
            reply_to,
        })
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.send(|reply_to| ChainRequest::IbcVersion { reply_to })
    }

    fn query_balance(
        &self,
        key_name: Option<String>,
        denom: Option<String>,
    ) -> Result<Balance, Error> {
        self.send(|reply_to| ChainRequest::QueryBalance {
            key_name,
            denom,
            reply_to,
        })
    }

    fn query_all_balances(&self, key_name: Option<String>) -> Result<Vec<Balance>, Error> {
        self.send(|reply_to| ChainRequest::QueryAllBalances { key_name, reply_to })
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        self.send(|reply_to| ChainRequest::QueryDenomTrace { hash, reply_to })
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        self.send(|reply_to| ChainRequest::QueryApplicationStatus { reply_to })
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.send(|reply_to| ChainRequest::QueryClients { request, reply_to })
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryClientState {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.send(|reply_to| ChainRequest::QueryClientConnections { request, reply_to })
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<Height>, Error> {
        self.send(|reply_to| ChainRequest::QueryConsensusStateHeights { request, reply_to })
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryConsensusState {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::QueryUpgradedClientState { request, reply_to })
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.send(|reply_to| ChainRequest::QueryUpgradedConsensusState { request, reply_to })
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.send(|reply_to| ChainRequest::QueryCommitmentPrefix { reply_to })
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.send(|reply_to| ChainRequest::QueryCompatibleVersions { reply_to })
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryConnection {
            request,
            include_proof,
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
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryNextSequenceReceive {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.send(|reply_to| ChainRequest::QueryChannels { request, reply_to })
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryChannel {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.send(|reply_to| ChainRequest::QueryChannelClientState { request, reply_to })
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
    ) -> Result<Proofs, Error> {
        self.send(|reply_to| ChainRequest::BuildPacketProofs {
            packet_type,
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
            height,
            reply_to,
        })
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketCommitment {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketCommitments { request, reply_to })
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketReceipt {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.send(|reply_to| ChainRequest::QueryUnreceivedPackets { request, reply_to })
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketAcknowledgement {
            request,
            include_proof,
            reply_to,
        })
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.send(|reply_to| ChainRequest::QueryPacketAcknowledgements { request, reply_to })
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.send(|reply_to| ChainRequest::QueryUnreceivedAcknowledgement { request, reply_to })
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.send(|reply_to| ChainRequest::QueryPacketEventDataFromTxs { request, reply_to })
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.send(|reply_to| ChainRequest::QueryPacketEventData { request, reply_to })
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error> {
        self.send(|reply_to| ChainRequest::QueryHostConsensusState { request, reply_to })
    }

    fn maybe_register_counterparty_payee(
        &self,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
    ) -> Result<(), Error> {
        self.send(|reply_to| ChainRequest::MaybeRegisterCounterpartyPayee {
            channel_id,
            port_id,
            counterparty_payee,
            reply_to,
        })
    }

    fn cross_chain_query(
        &self,
        request: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error> {
        self.send(|reply_to| ChainRequest::CrossChainQuery { request, reply_to })
    }
}
