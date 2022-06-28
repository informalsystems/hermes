use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use crate::clients::ics07_tendermint::client_def::TendermintClient;
use crate::core::ics02_client::client_consensus::ConsensusState;
use crate::core::ics02_client::client_state::ClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::context::LightClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::header::Header;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::context::ChannelMetaReader;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::prelude::*;
use crate::Height;

#[cfg(any(test, feature = "mocks"))]
use crate::mock::client_def::MockClient;

pub struct UpdatedState {
    pub client_state: Box<dyn ClientState>,
    pub consensus_state: Box<dyn ConsensusState>,
}

impl From<(Box<dyn ClientState>, Box<dyn ConsensusState>)> for UpdatedState {
    fn from(
        (client_state, consensus_state): (Box<dyn ClientState>, Box<dyn ConsensusState>),
    ) -> Self {
        Self {
            client_state,
            consensus_state,
        }
    }
}

pub trait ClientDef {
    fn check_header_and_update_state(
        &self,
        ctx: &dyn LightClientReader,
        client_id: ClientId,
        client_state: Box<dyn ClientState>,
        header: &dyn Header,
    ) -> Result<UpdatedState, Error>;

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &dyn ClientState,
        consensus_state: &dyn ConsensusState,
        proof_upgrade_client: MerkleProof,
        proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<UpdatedState, Error>;

    /// Verification functions as specified in:
    /// <https://github.com/cosmos/ibc/tree/master/spec/core/ics-002-client-semantics>
    ///
    /// Verify a `proof` that the consensus state of a given client (at height `consensus_height`)
    /// matches the input `consensus_state`. The parameter `counterparty_height` represent the
    /// height of the counterparty chain that this proof assumes (i.e., the height at which this
    /// proof was computed).
    #[allow(clippy::too_many_arguments)]
    fn verify_client_consensus_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a connection state matches that of the input `connection_end`.
    #[allow(clippy::too_many_arguments)]
    fn verify_connection_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a channel state matches that of the input `channel_end`.
    #[allow(clippy::too_many_arguments)]
    fn verify_channel_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error>;

    /// Verify the client state for this chain that it is stored on the counterparty chain.
    #[allow(clippy::too_many_arguments)]
    fn verify_client_full_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: &dyn ClientState,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_data(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack: AcknowledgementCommitment,
    ) -> Result<(), Error>;

    /// Verify a `proof` that of the next_seq_received.
    #[allow(clippy::too_many_arguments)]
    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has not been received.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error>;

    /// Decode the given protobuf encoded light-client header and return it.
    fn decode_header(&self, header: Any) -> Result<Box<dyn Header>, Error>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyClient {
    Tendermint(TendermintClient),

    #[cfg(any(test, feature = "mocks"))]
    Mock(MockClient),
}

impl AnyClient {
    pub fn from_client_type(client_type: ClientType) -> AnyClient {
        match client_type {
            ClientType::Tendermint => Self::Tendermint(TendermintClient::default()),

            #[cfg(any(test, feature = "mocks"))]
            ClientType::Mock => Self::Mock(MockClient),
        }
    }
}

// ⚠️  Beware of the awful boilerplate below ⚠️
impl ClientDef for AnyClient {
    /// Validates an incoming `header` against the latest consensus state of this client.
    fn check_header_and_update_state(
        &self,
        ctx: &dyn LightClientReader,
        client_id: ClientId,
        client_state: Box<dyn ClientState>,
        header: &dyn Header,
    ) -> Result<UpdatedState, Error> {
        match self {
            Self::Tendermint(client) => {
                client.check_header_and_update_state(ctx, client_id, client_state, header)
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                client.check_header_and_update_state(ctx, client_id, client_state, header)
            }
        }
    }

    fn verify_client_consensus_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_client_consensus_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                client_id,
                consensus_height,
                expected_consensus_state,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_client_consensus_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                client_id,
                consensus_height,
                expected_consensus_state,
            ),
        }
    }

    fn verify_connection_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_connection_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                connection_id,
                expected_connection_end,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_connection_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                connection_id,
                expected_connection_end,
            ),
        }
    }

    fn verify_channel_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_channel_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                port_id,
                channel_id,
                expected_channel_end,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_channel_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                port_id,
                channel_id,
                expected_channel_end,
            ),
        }
    }

    fn verify_client_full_state(
        &self,
        client_state: &dyn ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        client_state_on_counterparty: &dyn ClientState,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_client_full_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                client_id,
                client_state_on_counterparty,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_client_full_state(
                client_state,
                height,
                prefix,
                proof,
                root,
                client_id,
                client_state_on_counterparty,
            ),
        }
    }
    fn verify_packet_data(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_packet_data(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
                commitment,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_packet_data(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
                commitment,
            ),
        }
    }

    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack_commitment: AcknowledgementCommitment,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_packet_acknowledgement(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
                ack_commitment,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_packet_acknowledgement(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
                ack_commitment,
            ),
        }
    }

    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_next_sequence_recv(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_next_sequence_recv(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
            ),
        }
    }
    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ChannelMetaReader,
        client_state: &dyn ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_packet_receipt_absence(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
            ),
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_packet_receipt_absence(
                ctx,
                client_state,
                height,
                connection_end,
                proof,
                root,
                port_id,
                channel_id,
                sequence,
            ),
        }
    }

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &dyn ClientState,
        consensus_state: &dyn ConsensusState,
        proof_upgrade_client: MerkleProof,
        proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<UpdatedState, Error> {
        match self {
            Self::Tendermint(client) => client.verify_upgrade_and_update_state(
                client_state,
                consensus_state,
                proof_upgrade_client,
                proof_upgrade_consensus_state,
            ),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_upgrade_and_update_state(
                client_state,
                consensus_state,
                proof_upgrade_client,
                proof_upgrade_consensus_state,
            ),
        }
    }

    fn decode_header(&self, _header: Any) -> Result<Box<dyn Header>, Error> {
        todo!()
    }
}
