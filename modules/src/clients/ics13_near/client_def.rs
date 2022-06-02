use crate::clients::host_functions::HostFunctionsProvider;
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_def::{ClientDef, ConsensusUpdateResult};
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::core::ics26_routing::context::ReaderContext;
use crate::Height;
use core::marker::PhantomData;

use super::client_state::NearClientState;
use super::consensus_state::NearConsensusState;
use crate::core::ics02_client::error::Error;

use super::error::Error as NearError;
use super::header::NearHeader;
use super::types::{ApprovalInner, CryptoHash, LightClientBlockView};
use crate::prelude::*;

use borsh::BorshSerialize;

#[derive(Debug, Clone)]
pub struct NearClient<T: HostFunctionsProvider>(PhantomData<T>);

impl<T: HostFunctionsProvider> ClientDef for NearClient<T> {
    /// The data that we need to update the [`ClientState`] to a new block height
    type Header = NearHeader;

    /// The data that we need to know, to validate incoming headers and update the state
    /// of our [`ClientState`]. Ususally this will store:
    ///    - The current epoch
    ///    - The current validator set
    ///
    /// ```rust,no_run
    /// pub struct NearLightClientState {
    ///     head: LightClientBlockView,
    ///     current_validators: Vec<ValidatorStakeView>,
    ///     next_validators:  Vec<ValidatorStakeView>,
    /// }
    /// ```
    type ClientState = NearClientState;

    /// This is usually just two things, that should be derived from the header:
    ///    - The ibc commitment root hash as described by ics23 (possibly from tx outcome/ state proof)
    ///    - The timestamp of the header.
    type ConsensusState = NearConsensusState;

    // rehydrate client from its own storage, then call this function
    fn verify_header(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error> {
        // your light client, shouldn't do storage anymore, it should just do verification here.
        validate_light_block::<T>(&header, client_state)
    }

    fn update_state(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: ClientId,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        // 1. create new client state from this header, return that.
        // 2. as well as all the neccessary consensus states.
        //
        //
        // []--[]--[]--[]--[]--[]--[]--[]--[]--[]
        // 11  12  13  14  15  16  17  18  19  20 <- block merkle root
        // ^                                    ^
        // |    <-------consensus states----->  |
        // current state                       new state

        todo!()
    }

    fn update_state_on_misbehaviour(
        &self,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        todo!()
    }

    fn check_for_misbehaviour(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: ClientId,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<bool, Error> {
        Ok(false)
    }

    fn verify_upgrade_and_update_state(
        &self,
        _client_state: &Self::ClientState,
        _consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: Vec<u8>,
        _proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        _ctx: &dyn ReaderContext,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _consensus_height: Height,
        _expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error> {
        todo!()
    }

    // Consensus state will be verified in the verification functions  before these are called
    fn verify_connection_state(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _connection_id: &ConnectionId,
        _expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_channel_state(
        &self,
        _ctx: &dyn ReaderContext,
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
        todo!()
    }

    fn verify_client_full_state(
        &self,
        _ctx: &dyn ReaderContext,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _expected_client_state: &AnyClientState,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_packet_data(
        &self,
        _ctx: &dyn ReaderContext,
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
        todo!()
    }

    fn verify_packet_acknowledgement(
        &self,
        _ctx: &dyn ReaderContext,
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
        todo!()
    }

    fn verify_next_sequence_recv(
        &self,
        _ctx: &dyn ReaderContext,
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
        todo!()
    }

    fn verify_packet_receipt_absence(
        &self,
        _ctx: &dyn ReaderContext,
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
        todo!()
    }
}

/// validates a light block that's contained on the `NearHeader` based on the current
/// state of the light client.
pub fn validate_light_block<H: HostFunctionsProvider>(
    header: &NearHeader,
    client_state: NearClientState,
) -> Result<(), Error> {
    //The light client updates its head with the information from LightClientBlockView iff:

    // 1. The height of the block is higher than the height of the current head;
    // 2. The epoch of the block is equal to the epoch_id or next_epoch_id known for the current head;
    // 3. If the epoch of the block is equal to the next_epoch_id of the head, then next_bps is not None;
    // 4. approvals_after_next contain valid signatures on approval_message from the block producers of the corresponding
    // epoch
    // 5. The signatures present in approvals_after_next correspond to more than 2/3 of the total stake (see next section).
    // 6. If next_bps is not none, sha256(borsh(next_bps)) corresponds to the next_bp_hash in inner_lite.

    // QUESTION: do we also want to pass the block hash received from the RPC?
    // it's not on the spec, but it's an extra validation

    let new_block_view = header.get_light_client_block_view();
    let current_block_view = client_state.get_head();
    let (_current_block_hash, _next_block_hash, approval_message) =
        reconstruct_light_client_block_view_fields::<H>(new_block_view)?;

    // (1)
    if new_block_view.inner_lite.height <= current_block_view.inner_lite.height {
        return Err(NearError::height_too_old().into());
    }

    // (2)
    if ![
        current_block_view.inner_lite.epoch_id,
        current_block_view.inner_lite.next_epoch_id,
    ]
    .contains(&new_block_view.inner_lite.epoch_id)
    {
        return Err(NearError::invalid_epoch(new_block_view.inner_lite.epoch_id).into());
    }

    // (3)
    if new_block_view.inner_lite.epoch_id == current_block_view.inner_lite.next_epoch_id
        && new_block_view.next_bps.is_none()
    {
        return Err(NearError::unavailable_block_producers().into());
    }

    //  (4) and (5)
    let mut total_stake = 0;
    let mut approved_stake = 0;

    let epoch_block_producers = client_state
        .get_validators_by_epoch(&new_block_view.inner_lite.epoch_id)
        .ok_or_else(|| Error::from(NearError::invalid_epoch(new_block_view.inner_lite.epoch_id)))?;

    for (maybe_signature, block_producer) in new_block_view
        .approvals_after_next
        .iter()
        .zip(epoch_block_producers.iter())
    {
        let bp_stake_view = block_producer.clone().into_validator_stake();
        let bp_stake = bp_stake_view.stake;
        total_stake += bp_stake;

        if maybe_signature.is_none() {
            continue;
        }

        approved_stake += bp_stake;

        let validator_public_key = &bp_stake_view.public_key;
        let data = H::sha256_digest(&approval_message);
        let signature = maybe_signature.as_ref().unwrap();
        if H::ed25519_verify(
            signature.get_inner(),
            &data,
            validator_public_key.get_inner(),
        ) {
            return Err(NearError::invalid_signature().into());
        }
    }

    let threshold = total_stake * 2 / 3;
    if approved_stake <= threshold {
        return Err(NearError::insufficient_staked_amount().into());
    }

    // # (6)
    if new_block_view.next_bps.is_some() {
        let new_block_view_next_bps_serialized = new_block_view
            .next_bps
            .as_deref()
            .unwrap()
            .try_to_vec()
            .map_err(|_| Error::from(NearError::serialization_error()))?;
        if H::sha256_digest(new_block_view_next_bps_serialized.as_ref()).as_slice()
            != new_block_view.inner_lite.next_bp_hash.as_ref()
        {
            return Err(NearError::serialization_error().into());
        }
    }
    Ok(())
}

pub fn reconstruct_light_client_block_view_fields<H: HostFunctionsProvider>(
    block_view: &LightClientBlockView,
) -> Result<(CryptoHash, CryptoHash, Vec<u8>), Error> {
    let current_block_hash = block_view.current_block_hash::<H>();
    let next_block_hash =
        next_block_hash::<H>(block_view.next_block_inner_hash, current_block_hash);
    let approval_message = [
        ApprovalInner::Endorsement(next_block_hash)
            .try_to_vec()
            .map_err(|_| Error::from(NearError::serialization_error()))?,
        (block_view.inner_lite.height + 2)
            .to_le()
            .try_to_vec()
            .map_err(|_| Error::from(NearError::serialization_error()))?,
    ]
    .concat();
    Ok((current_block_hash, next_block_hash, approval_message))
}

pub(crate) fn next_block_hash<H: HostFunctionsProvider>(
    next_block_inner_hash: CryptoHash,
    current_block_hash: CryptoHash,
) -> CryptoHash {
    H::sha256_digest(
        [next_block_inner_hash.as_ref(), current_block_hash.as_ref()]
            .concat()
            .as_ref(),
    )
    .as_slice()
    .try_into()
    .expect("Could not hash the next block")
}
