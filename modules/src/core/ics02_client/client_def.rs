use crate::core::ics02_client::{client_consensus::ConsensusState, client_state::ClientState};

use crate::core::ics02_client::context::ClientTypes;
use crate::{
	core::{
		ics02_client::{client_message::ClientMessage, error::Error},
		ics03_connection::connection::ConnectionEnd,
		ics04_channel::{
			channel::ChannelEnd,
			commitment::{AcknowledgementCommitment, PacketCommitment},
			packet::Sequence,
		},
		ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes, CommitmentRoot},
		ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
		ics26_routing::context::ReaderContext,
	},
	prelude::*,
	Height,
};
use core::fmt::Debug;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ConsensusUpdateResult<C: ClientTypes> {
	Single(C::AnyConsensusState),
	Batch(Vec<(Height, C::AnyConsensusState)>),
}

impl<C: ClientTypes> ConsensusUpdateResult<C> {
	pub fn map_state<F, D: ClientTypes>(self, f: F) -> ConsensusUpdateResult<D>
	where
		F: Fn(C::AnyConsensusState) -> D::AnyConsensusState,
	{
		match self {
			ConsensusUpdateResult::Single(cs) => ConsensusUpdateResult::Single(f(cs)),
			ConsensusUpdateResult::Batch(cs) => {
				ConsensusUpdateResult::Batch(cs.into_iter().map(|(h, s)| (h, f(s))).collect())
			},
		}
	}
}

pub trait ClientDef: Clone {
	type ClientMessage: ClientMessage;
	type ClientState: ClientState<ClientDef = Self> + Eq;
	type ConsensusState: ConsensusState + Eq;

	fn verify_client_message<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: ClientId,
		client_state: Self::ClientState,
		client_msg: Self::ClientMessage,
	) -> Result<(), Error>;

	fn update_state<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: ClientId,
		client_state: Self::ClientState,
		client_msg: Self::ClientMessage,
	) -> Result<(Self::ClientState, ConsensusUpdateResult<Ctx>), Error>;

	fn update_state_on_misbehaviour(
		&self,
		client_state: Self::ClientState,
		client_msg: Self::ClientMessage,
	) -> Result<Self::ClientState, Error>;

	fn check_for_misbehaviour<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: ClientId,
		client_state: Self::ClientState,
		client_msg: Self::ClientMessage,
	) -> Result<bool, Error>;

	fn verify_upgrade_and_update_state<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: ClientId,
		old_client_state: &Self::ClientState,
		upgrade_client_state: &Self::ClientState,
		upgrade_consensus_state: &Self::ConsensusState,
		proof_upgrade_client: Vec<u8>,
		proof_upgrade_consensus_state: Vec<u8>,
	) -> Result<(Self::ClientState, ConsensusUpdateResult<Ctx>), Error>;

	/// Verification functions as specified in:
	/// <https://github.com/cosmos/ibc/tree/master/spec/core/ics-002-client-semantics>
	///
	/// Verify a `proof` that the consensus state of a given client (at height `consensus_height`)
	/// matches the input `consensus_state`. The parameter `counterparty_height` represent the
	/// height of the counterparty chain that this proof assumes (i.e., the height at which this
	/// proof was computed).
	#[allow(clippy::too_many_arguments)]
	fn verify_client_consensus_state<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_state: &Self::ClientState,
		height: Height,
		prefix: &CommitmentPrefix,
		proof: &CommitmentProofBytes,
		root: &CommitmentRoot,
		client_id: &ClientId,
		consensus_height: Height,
		expected_consensus_state: &Ctx::AnyConsensusState,
	) -> Result<(), Error>;

	/// Verify a `proof` that a connection state matches that of the input `connection_end`.
	#[allow(clippy::too_many_arguments)]
	fn verify_connection_state<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: &ClientId,
		client_state: &Self::ClientState,
		height: Height,
		prefix: &CommitmentPrefix,
		proof: &CommitmentProofBytes,
		root: &CommitmentRoot,
		connection_id: &ConnectionId,
		expected_connection_end: &ConnectionEnd,
	) -> Result<(), Error>;

	/// Verify a `proof` that a channel state matches that of the input `channel_end`.
	#[allow(clippy::too_many_arguments)]
	fn verify_channel_state<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: &ClientId,
		client_state: &Self::ClientState,
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
	fn verify_client_full_state<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_state: &Self::ClientState,
		height: Height,
		prefix: &CommitmentPrefix,
		proof: &CommitmentProofBytes,
		root: &CommitmentRoot,
		client_id: &ClientId,
		expected_client_state: &Ctx::AnyClientState,
	) -> Result<(), Error>;

	/// Verify a `proof` that a packet has been commited.
	#[allow(clippy::too_many_arguments)]
	fn verify_packet_data<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: &ClientId,
		client_state: &Self::ClientState,
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
	fn verify_packet_acknowledgement<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: &ClientId,
		client_state: &Self::ClientState,
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
	fn verify_next_sequence_recv<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: &ClientId,
		client_state: &Self::ClientState,
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
	fn verify_packet_receipt_absence<Ctx: ReaderContext>(
		&self,
		ctx: &Ctx,
		client_id: &ClientId,
		client_state: &Self::ClientState,
		height: Height,
		connection_end: &ConnectionEnd,
		proof: &CommitmentProofBytes,
		root: &CommitmentRoot,
		port_id: &PortId,
		channel_id: &ChannelId,
		sequence: Sequence,
	) -> Result<(), Error>;
}
