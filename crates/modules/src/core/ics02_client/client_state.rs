use core::marker::{Send, Sync};
use core::time::Duration;

use dyn_clone::DynClone;
use erased_serde::Serialize as ErasedSerialize;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::protobuf::Protobuf as ErasedProtobuf;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use crate::dynamic_typing::AsAny;
use crate::prelude::*;
use crate::Height;

use super::consensus_state::ConsensusState;
use super::context::ClientReader;

pub trait ClientState:
    AsAny
    + sealed::ErasedPartialEqClientState
    + DynClone
    + ErasedSerialize
    + ErasedProtobuf<Any, Error = Error>
    + core::fmt::Debug
    + Send
    + Sync
{
    /// Return the chain identifier which this client is serving (i.e., the client is verifying
    /// consensus states from this chain).
    fn chain_id(&self) -> ChainId;

    /// Type of client associated with this state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Latest height the client was updated to
    fn latest_height(&self) -> Height;

    /// Freeze status of the client
    fn is_frozen(&self) -> bool {
        self.frozen_height().is_some()
    }

    /// Frozen height of the client
    fn frozen_height(&self) -> Option<Height>;

    /// Check if the state is expired when `elapsed` time has passed since the latest consensus
    /// state timestamp
    fn expired(&self, elapsed: Duration) -> bool;

    /// Helper function to verify the upgrade client procedure.
    /// Resets all fields except the blockchain-specific ones,
    /// and updates the given fields.
    fn upgrade(
        &mut self,
        upgrade_height: Height,
        upgrade_options: &dyn UpgradeOptions,
        chain_id: ChainId,
    );

    /// Convert into a boxed trait object
    fn into_box(self) -> Box<dyn ClientState>
    where
        Self: Sized,
    {
        Box::new(self)
    }

    fn initialise(&self, consensus_state: Any) -> Result<Box<dyn ConsensusState>, Error>;

    fn check_header_and_update_state(
        &self,
        ctx: &dyn ClientReader,
        client_id: ClientId,
        header: Any,
    ) -> Result<UpdatedState, Error>;

    fn verify_upgrade_and_update_state(
        &self,
        consensus_state: Any,
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
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: Any,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_data(
        &self,
        ctx: &dyn ChannelReader,
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
        ctx: &dyn ChannelReader,
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
        ctx: &dyn ChannelReader,
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
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error>;
}

// Implements `Clone` for `Box<dyn ClientState>`
dyn_clone::clone_trait_object!(ClientState);

// Implements `serde::Serialize` for all types that have ClientState as supertrait
erased_serde::serialize_trait_object!(ClientState);

impl PartialEq for dyn ClientState {
    fn eq(&self, other: &Self) -> bool {
        self.eq_client_state(other)
    }
}

// see https://github.com/rust-lang/rust/issues/31740
impl PartialEq<&Self> for Box<dyn ClientState> {
    fn eq(&self, other: &&Self) -> bool {
        self.eq_client_state(other.as_ref())
    }
}

pub fn downcast_client_state<CS: ClientState>(h: &dyn ClientState) -> Option<&CS> {
    h.as_any().downcast_ref::<CS>()
}

pub trait UpgradeOptions: AsAny {}

pub struct UpdatedState {
    pub client_state: Box<dyn ClientState>,
    pub consensus_state: Box<dyn ConsensusState>,
}

mod sealed {
    use super::*;

    pub trait ErasedPartialEqClientState {
        fn eq_client_state(&self, other: &dyn ClientState) -> bool;
    }

    impl<CS> ErasedPartialEqClientState for CS
    where
        CS: ClientState + PartialEq,
    {
        fn eq_client_state(&self, other: &dyn ClientState) -> bool {
            other
                .as_any()
                .downcast_ref::<CS>()
                .map_or(false, |h| self == h)
        }
    }
}
