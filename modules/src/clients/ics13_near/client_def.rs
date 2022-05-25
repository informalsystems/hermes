use crate::clients::host_functions::HostFunctionsProvider;
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_def::{ClientDef, ConsensusUpdateResult};
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics24_host::identifier::ClientId;
use crate::core::ics26_routing::context::LightClientContext;
use std::marker::PhantomData;

use super::client_state::NearClientState;
use super::consensus_state::NearConsensusState;
use super::crypto_ops::NearCryptoOps;
use super::error::Error;
use super::header::NearHeader;
use super::types::{ApprovalInner, CryptoHash, LightClientBlockView, ValidatorStakeView};

#[derive(Debug, Clone)]
pub struct NearClient<HostFunctions>(PhantomData<HostFunctions>);

impl<HostFunctions: HostFunctions> ClientDef for NearClient<HostFunctions> {
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
        _ctx: &dyn LightClientContext,
        _client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error> {
        // your light client, shouldn't do storage anymore, it should just do verification here.
        validate_light_block(&header, client_state)
    }

    fn update_state(
        &self,
        ctx: &dyn LightClientContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
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
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        todo!()
    }

    fn check_for_misbehaviour(
        &self,
        _ctx: &dyn LightClientContext,
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
        _ctx: &dyn LightClientContext,
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
        _ctx: &dyn LightClientContext,
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
        _ctx: &dyn LightClientContext,
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
        _ctx: &dyn LightClientContext,
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
        ctx: &dyn LightClientContext,
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
        ctx: &dyn LightClientContext,
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
        _ctx: &dyn LightClientContext,
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
        _ctx: &dyn LightClientContext,
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

// TODO: refactor to use [`HostFunctions`]
pub fn validate_light_block<D: Digest>(
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
    let current_block_view = client_state.get_head().get_light_client_block_view();
    let (_current_block_hash, _next_block_hash, approval_message) =
        reconstruct_light_client_block_view_fields::<D>(new_block_view)?;

    // (1)
    if new_block_view.inner_lite.height <= current_block_view.inner_lite.height {
        return Err(Error::HeightTooOld);
    }

    // (2)
    if ![
        current_block_view.inner_lite.epoch_id,
        current_block_view.inner_lite.next_epoch_id,
    ]
    .contains(&new_block_view.inner_lite.epoch_id)
    {
        return Err(Error::InvalidEpoch);
    }

    // (3)
    if new_block_view.inner_lite.epoch_id == current_block_view.inner_lite.next_epoch_id
        && new_block_view.next_bps.is_none()
    {
        return Err(Error::UnavailableBlockProducers);
    }

    //  (4) and (5)
    let mut total_stake = 0;
    let mut approved_stake = 0;

    let epoch_block_producers = client_state
        .get_validators_by_epoch(&new_block_view.inner_lite.epoch_id)
        .ok_or(Error::InvalidEpoch)?;

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

        let validator_public_key = bp_stake_view.public_key.clone();
        if !maybe_signature
            .as_ref()
            .unwrap()
            .verify(&approval_message, validator_public_key.clone())
        {
            return Err(Error::InvalidSignature);
        }
    }

    let threshold = total_stake * 2 / 3;
    if approved_stake <= threshold {
        return Err(Error::InsufficientStakedAmount);
    }

    // # (6)
    if new_block_view.next_bps.is_some() {
        let new_block_view_next_bps_serialized =
            new_block_view.next_bps.as_deref().unwrap().try_to_vec()?;
        if D::digest(new_block_view_next_bps_serialized).as_slice()
            != new_block_view.inner_lite.next_bp_hash.as_ref()
        {
            return Err(Error::SerializationError);
        }
    }
    Ok(())
}

pub fn reconstruct_light_client_block_view_fields<D: Digest>(
    block_view: &LightClientBlockView,
) -> Result<(CryptoHash, CryptoHash, Vec<u8>), Error> {
    let current_block_hash = block_view.current_block_hash::<D>();
    let next_block_hash =
        next_block_hash::<D>(block_view.next_block_inner_hash, current_block_hash);
    let approval_message = [
        ApprovalInner::Endorsement(next_block_hash).try_to_vec()?,
        (block_view.inner_lite.height + 2).to_le().try_to_vec()?,
    ]
    .concat();
    Ok((current_block_hash, next_block_hash, approval_message))
}

pub(crate) fn next_block_hash<D: Digest>(
    next_block_inner_hash: CryptoHash,
    current_block_hash: CryptoHash,
) -> CryptoHash {
    D::digest([next_block_inner_hash.as_ref(), current_block_hash.as_ref()].concat())
        .as_slice()
        .try_into()
        .expect("Could not hash the next block")
}
