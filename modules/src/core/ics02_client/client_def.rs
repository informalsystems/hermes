use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use crate::clients::ics07_tendermint::client_def::TendermintClient;
use crate::core::ics02_client::client_consensus::{AnyConsensusState, ConsensusState};
use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::context::ClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::header::{AnyHeader, Header};
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics23_commitment::merkle::{self, apply_prefix};
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::core::ics24_host::path::{
    AcksPath, ChannelEndsPath, ClientConsensusStatePath, ClientStatePath, CommitmentsPath,
    ConnectionsPath, ReceiptsPath, SeqRecvsPath,
};
use crate::core::ics24_host::Path;
use crate::downcast;
use crate::prelude::*;
use crate::Height;
use prost::Message;
use tendermint_proto::Protobuf;

#[cfg(any(test, feature = "mocks"))]
use crate::mock::client_def::MockClient;

pub trait ClientDef: Clone {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;

    fn check_header_and_update_state(
        &self,
        ctx: &dyn ClientReader,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Error>;

    /// TODO
    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        proof_upgrade_client: MerkleProof,
        proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Error>;

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
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;

        let path = ClientConsensusStatePath {
            client_id: client_id.clone(),
            epoch: consensus_height.revision_number,
            height: consensus_height.revision_height,
        };
        let value = expected_consensus_state
            .encode_vec()
            .map_err(Error::invalid_any_consensus_state)?;
        self.verify_membership(client_state, prefix, proof, root, path, value)
    }

    /// Verify a `proof` that a connection state matches that of the input `connection_end`.
    #[allow(clippy::too_many_arguments)]
    fn verify_connection_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;

        let path = ConnectionsPath(connection_id.clone());
        let value = expected_connection_end
            .encode_vec()
            .map_err(Error::invalid_connection_end)?;
        self.verify_membership(client_state, prefix, proof, root, path, value)
    }

    /// Verify a `proof` that a channel state matches that of the input `channel_end`.
    #[allow(clippy::too_many_arguments)]
    fn verify_channel_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;

        let path = ChannelEndsPath(port_id.clone(), *channel_id);
        let value = expected_channel_end
            .encode_vec()
            .map_err(Error::invalid_channel_end)?;

        self.verify_membership(client_state, prefix, proof, root, path, value)
    }

    /// Verify the client state for this chain that it is stored on the counterparty chain.
    #[allow(clippy::too_many_arguments)]
    fn verify_client_full_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: &AnyClientState,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;

        let path = ClientStatePath(client_id.clone());
        let value = expected_client_state
            .encode_vec()
            .map_err(Error::invalid_any_client_state)?;

        self.verify_membership(client_state, prefix, proof, root, path, value)
    }

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_data(
        &self,
        ctx: &dyn ChannelReader,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: String,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        self.verify_delay_passed(ctx, height, connection_end)?;

        let commitment_path = CommitmentsPath {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
        };

        let mut commitment_bytes = Vec::new();
        commitment
            .encode(&mut commitment_bytes)
            .expect("buffer size too small");

        self.verify_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            commitment_path,
            commitment_bytes,
        )
    }

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ChannelReader,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack: Acknowledgement,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        self.verify_delay_passed(ctx, height, connection_end)?;

        let ack_path = AcksPath {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
        };
        self.verify_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            ack_path,
            ack.into_bytes(),
        )
    }

    /// Verify a `proof` that of the next_seq_received.
    #[allow(clippy::too_many_arguments)]
    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ChannelReader,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        self.verify_delay_passed(ctx, height, connection_end)?;

        let mut seq_bytes = Vec::new();
        u64::from(sequence)
            .encode(&mut seq_bytes)
            .expect("buffer size too small");

        let seq_path = SeqRecvsPath(port_id.clone(), *channel_id);
        self.verify_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            seq_path,
            seq_bytes,
        )
    }

    /// Verify a `proof` that a packet has not been received.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ChannelReader,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        self.verify_delay_passed(ctx, height, connection_end)?;

        let receipt_path = ReceiptsPath {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
        };
        self.verify_non_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            receipt_path,
        )
    }

    fn verify_membership(
        &self,
        client_state: &Self::ClientState,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        path: impl Into<Path>,
        value: Vec<u8>,
    ) -> Result<(), Error> {
        let merkle_path = apply_prefix(prefix, vec![path.into().to_string()]);
        let merkle_proof: merkle::MerkleProof = MerkleProof::try_from(proof.clone())
            .map_err(Error::invalid_commitment_proof)?
            .into();

        merkle_proof
            .verify_membership(
                client_state.proof_specs(),
                root.clone().into(),
                merkle_path,
                value,
                0,
            )
            .map_err(Error::ics23_error)
    }

    fn verify_non_membership(
        &self,
        client_state: &Self::ClientState,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        path: impl Into<Path>,
    ) -> Result<(), Error> {
        let merkle_path = apply_prefix(prefix, vec![path.into().to_string()]);
        let merkle_proof: merkle::MerkleProof = MerkleProof::try_from(proof.clone())
            .map_err(Error::invalid_commitment_proof)?
            .into();

        merkle_proof
            .verify_non_membership(client_state.proof_specs(), root.clone().into(), merkle_path)
            .map_err(Error::ics23_error)
    }

    fn verify_delay_passed(
        &self,
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
    ) -> Result<(), Error>;
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
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;

    /// Validates an incoming `header` against the latest consensus state of this client.
    fn check_header_and_update_state(
        &self,
        ctx: &dyn ClientReader,
        client_id: ClientId,
        client_state: AnyClientState,
        header: AnyHeader,
    ) -> Result<(AnyClientState, AnyConsensusState), Error> {
        match self {
            Self::Tendermint(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    header => AnyHeader::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                let (new_state, new_consensus) =
                    client.check_header_and_update_state(ctx, client_id, client_state, header)?;

                Ok((
                    AnyClientState::Tendermint(new_state),
                    AnyConsensusState::Tendermint(new_consensus),
                ))
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Mock,
                    header => AnyHeader::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                let (new_state, new_consensus) =
                    client.check_header_and_update_state(ctx, client_id, client_state, header)?;

                Ok((
                    AnyClientState::Mock(new_state),
                    AnyConsensusState::Mock(new_consensus),
                ))
            }
        }
    }

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        proof_upgrade_client: MerkleProof,
        proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Error> {
        match self {
            Self::Tendermint(client) => {
                let (client_state, consensus_state) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    consensus_state => AnyConsensusState::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                let (new_state, new_consensus) = client.verify_upgrade_and_update_state(
                    client_state,
                    consensus_state,
                    proof_upgrade_client,
                    proof_upgrade_consensus_state,
                )?;

                Ok((
                    AnyClientState::Tendermint(new_state),
                    AnyConsensusState::Tendermint(new_consensus),
                ))
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let (client_state, consensus_state) = downcast!(
                    client_state => AnyClientState::Mock,
                    consensus_state => AnyConsensusState::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                let (new_state, new_consensus) = client.verify_upgrade_and_update_state(
                    client_state,
                    consensus_state,
                    proof_upgrade_client,
                    proof_upgrade_consensus_state,
                )?;

                Ok((
                    AnyClientState::Mock(new_state),
                    AnyConsensusState::Mock(new_consensus),
                ))
            }
        }
    }

    fn verify_delay_passed(
        &self,
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => client.verify_delay_passed(ctx, height, connection_end),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => client.verify_delay_passed(ctx, height, connection_end),
        }
    }
}
