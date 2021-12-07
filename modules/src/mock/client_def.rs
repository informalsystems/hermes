use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_def::ClientDef;
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::context::ClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{CommitmentPrefix, CommitmentRoot};
use crate::core::ics23_commitment::merkle::apply_prefix;
use crate::core::ics24_host::identifier::ClientId;
use crate::core::ics24_host::Path;
use crate::mock::client_state::{MockClientState, MockConsensusState};
use crate::mock::header::MockHeader;
use crate::prelude::*;
use crate::proofs::Proofs;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockClient;

impl ClientDef for MockClient {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;

    fn check_header_and_update_state(
        &self,
        _ctx: &dyn ClientReader,
        _client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Error> {
        if client_state.latest_height() >= header.height() {
            return Err(Error::low_header_height(
                header.height(),
                client_state.latest_height(),
            ));
        }
        Ok((
            MockClientState::new(header),
            MockConsensusState::new(header),
        ))
    }

    fn verify_client_consensus_state(
        &self,
        _client_state: &Self::ClientState,
        prefix: &CommitmentPrefix,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        consensus_state_path: &Path,
        _expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error> {
        let _path = apply_prefix(prefix, vec![consensus_state_path.to_string()])
            .map_err(Error::empty_prefix)?;

        Ok(())
    }

    fn verify_connection_state(
        &self,
        _client_state: &Self::ClientState,
        _prefix: &CommitmentPrefix,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _connection_path: &Path,
        _expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_channel_state(
        &self,
        _client_state: &Self::ClientState,
        _prefix: &CommitmentPrefix,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _channel_path: &Path,
        _expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_client_full_state(
        &self,
        _client_state: &Self::ClientState,
        _prefix: &CommitmentPrefix,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _client_state_path: &Path,
        _expected_client_state: &AnyClientState,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_data(
        &self,
        _ctx: &dyn ChannelReader,
        _client_state: &Self::ClientState,
        _connection_end: &ConnectionEnd,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _commitment_path: &Path,
        _commitment: String,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_acknowledgement(
        &self,
        _ctx: &dyn ChannelReader,
        _client_state: &Self::ClientState,
        _connection_end: &ConnectionEnd,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _ack_path: &Path,
        _ack: Vec<u8>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_next_sequence_recv(
        &self,
        _ctx: &dyn ChannelReader,
        _client_state: &Self::ClientState,
        _connection_end: &ConnectionEnd,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _seq_path: &Path,
        _seq: Sequence,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_receipt_absence(
        &self,
        _ctx: &dyn ChannelReader,
        _client_state: &Self::ClientState,
        _connection_end: &ConnectionEnd,
        _proofs: &Proofs,
        _root: &CommitmentRoot,
        _receipt_path: &Path,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: MerkleProof,
        _proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Error> {
        Ok((*client_state, consensus_state.clone()))
    }
}
