use crate::core::ics02_client::{
	client_consensus::ConsensusState,
	client_def::{ClientDef, ConsensusUpdateResult},
};

use crate::mock::header::MockClientMessage;
use crate::{
	core::{
		ics02_client::error::Error,
		ics03_connection::connection::ConnectionEnd,
		ics04_channel::{
			channel::ChannelEnd,
			commitment::{AcknowledgementCommitment, PacketCommitment},
			packet::Sequence,
		},
		ics23_commitment::{
			commitment::{CommitmentPrefix, CommitmentProofBytes, CommitmentRoot},
			merkle::apply_prefix,
		},
		ics24_host::{
			identifier::{ChannelId, ClientId, ConnectionId, PortId},
			path::ClientConsensusStatePath,
			Path,
		},
		ics26_routing::context::ReaderContext,
	},
	mock::{
		client_state::{AnyClientState, AnyConsensusState, MockClientState, MockConsensusState},
		header::AnyClientMessage,
	},
	prelude::*,
	Height,
};
use core::fmt::Debug;

#[derive(Clone, Debug, PartialEq, Eq, ClientDef)]
pub enum AnyClient {
	Mock(MockClient),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockClient;

impl Default for MockClient {
	fn default() -> Self {
		Self
	}
}

impl ClientDef for MockClient {
	type ClientMessage = MockClientMessage;
	type ClientState = MockClientState;
	type ConsensusState = MockConsensusState;

	fn update_state<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: ClientId,
		client_state: Self::ClientState,
		client_message: Self::ClientMessage,
	) -> Result<(Self::ClientState, ConsensusUpdateResult<Ctx>), Error> {
		if client_state.latest_height() >= client_message.height() {
			return Err(Error::low_header_height(
				client_message.height(),
				client_state.latest_height(),
			));
		}

		let header = client_message.header();
		Ok((
			MockClientState::new(client_message),
			ConsensusUpdateResult::Single(
				Ctx::AnyConsensusState::wrap(&MockConsensusState::new(header)).unwrap(),
			),
		))
	}

	fn verify_client_consensus_state<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_state: &Self::ClientState,
		_height: Height,
		prefix: &CommitmentPrefix,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		client_id: &ClientId,
		consensus_height: Height,
		_expected_consensus_state: &Ctx::AnyConsensusState,
	) -> Result<(), Error> {
		let client_prefixed_path = Path::ClientConsensusState(ClientConsensusStatePath {
			client_id: client_id.clone(),
			epoch: consensus_height.revision_number,
			height: consensus_height.revision_height,
		})
		.to_string();

		let _path = apply_prefix(prefix, vec![client_prefixed_path]);

		Ok(())
	}

	fn verify_connection_state<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: &ClientId,
		_client_state: &Self::ClientState,
		_height: Height,
		_prefix: &CommitmentPrefix,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_connection_id: &ConnectionId,
		_expected_connection_end: &ConnectionEnd,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_channel_state<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: &ClientId,
		_client_state: &Self::ClientState,
		_height: Height,
		_prefix: &CommitmentPrefix,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_port_id: &PortId,
		_channel_id: &ChannelId,
		_expected_channel_end: &ChannelEnd,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_client_full_state<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_state: &Self::ClientState,
		_height: Height,
		_prefix: &CommitmentPrefix,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_client_id: &ClientId,
		_expected_client_state: &Ctx::AnyClientState,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_packet_data<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: &ClientId,
		_client_state: &Self::ClientState,
		_height: Height,
		_connection_end: &ConnectionEnd,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_port_id: &PortId,
		_channel_id: &ChannelId,
		_sequence: Sequence,
		_commitment: PacketCommitment,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_packet_acknowledgement<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: &ClientId,
		_client_state: &Self::ClientState,
		_height: Height,
		_connection_end: &ConnectionEnd,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_port_id: &PortId,
		_channel_id: &ChannelId,
		_sequence: Sequence,
		_ack: AcknowledgementCommitment,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_next_sequence_recv<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: &ClientId,
		_client_state: &Self::ClientState,
		_height: Height,
		_connection_end: &ConnectionEnd,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_port_id: &PortId,
		_channel_id: &ChannelId,
		_sequence: Sequence,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_packet_receipt_absence<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: &ClientId,
		_client_state: &Self::ClientState,
		_height: Height,
		_connection_end: &ConnectionEnd,
		_proof: &CommitmentProofBytes,
		_root: &CommitmentRoot,
		_port_id: &PortId,
		_channel_id: &ChannelId,
		_sequence: Sequence,
	) -> Result<(), Error> {
		Ok(())
	}

	fn verify_upgrade_and_update_state<Ctx: ReaderContext>(
		&self,
		client_state: &Self::ClientState,
		consensus_state: &Self::ConsensusState,
		_proof_upgrade_client: Vec<u8>,
		_proof_upgrade_consensus_state: Vec<u8>,
	) -> Result<(Self::ClientState, ConsensusUpdateResult<Ctx>), Error> {
		Ok((
			*client_state,
			ConsensusUpdateResult::Single(Ctx::AnyConsensusState::wrap(consensus_state).unwrap()),
		))
	}

	fn verify_client_message<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: ClientId,
		_client_state: Self::ClientState,
		_client_msg: Self::ClientMessage,
	) -> Result<(), Error> {
		Ok(())
	}

	fn update_state_on_misbehaviour(
		&self,
		client_state: Self::ClientState,
		_client_msg: Self::ClientMessage,
	) -> Result<Self::ClientState, Error> {
		Ok(client_state)
	}

	fn check_for_misbehaviour<Ctx: ReaderContext>(
		&self,
		_ctx: &Ctx,
		_client_id: ClientId,
		_client_state: Self::ClientState,
		_client_msg: Self::ClientMessage,
	) -> Result<bool, Error> {
		Ok(false)
	}
}
