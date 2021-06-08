//! ICS3 verification functions, common across all four handlers of ICS3.

use crate::ics02_client::client_consensus::ConsensusState;
use crate::ics02_client::client_state::{AnyClientState, ClientState};
use crate::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error;
use crate::ics23_commitment::commitment::CommitmentProofBytes;
use crate::proofs::{ConsensusProof, Proofs};
use crate::Height;

/// Entry point for verifying all proofs bundled in any ICS3 message.
pub fn verify_proofs(
    ctx: &dyn ConnectionReader,
    client_state: Option<AnyClientState>,
    connection_end: &ConnectionEnd,
    expected_conn: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), error::Error> {
    verify_connection_proof(
        ctx,
        connection_end,
        expected_conn,
        proofs.height(),
        proofs.object_proof(),
    )?;

    // If the message includes a client state, then verify the proof for that state.
    if let Some(expected_client_state) = client_state {
        verify_client_proof(
            ctx,
            connection_end,
            expected_client_state,
            proofs.height(),
            proofs
                .client_proof()
                .as_ref()
                .ok_or_else(error::null_client_proof_error)?,
        )?;
    }

    // If a consensus proof is attached to the message, then verify it.
    if let Some(proof) = proofs.consensus_proof() {
        Ok(verify_consensus_proof(
            ctx,
            connection_end,
            proofs.height(),
            &proof,
        )?)
    } else {
        Ok(())
    }
}

/// Verifies the authenticity and semantic correctness of a commitment `proof`. The commitment
/// claims to prove that an object of type connection exists on the source chain (i.e., the chain
/// which created this proof). This object must match the state of `expected_conn`.
pub fn verify_connection_proof(
    ctx: &dyn ConnectionReader,
    connection_end: &ConnectionEnd,
    expected_conn: &ConnectionEnd,
    proof_height: Height,
    proof: &CommitmentProofBytes,
) -> Result<(), error::Error> {
    // Fetch the client state (IBC client on the local/host chain).
    let client_state = ctx
        .client_state(connection_end.client_id())
        .ok_or_else(|| error::missing_client_error(connection_end.client_id().clone()))?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(error::frozen_client_error(
            connection_end.client_id().clone(),
        ));
    }

    // The client must have the consensus state for the height where this proof was created.
    if ctx
        .client_consensus_state(connection_end.client_id(), proof_height)
        .is_none()
    {
        return Err(error::missing_client_consensus_state_error(
            proof_height,
            connection_end.client_id().clone(),
        ));
    }

    let client_def = AnyClient::from_client_type(client_state.client_type());

    // Verify the proof for the connection state against the expected connection end.
    // A counterparty connection id of None causes `unwrap()` below and indicates an internal
    // error as this is the connection id on the counterparty chain that must always be present.
    client_def
        .verify_connection_state(
            &client_state,
            proof_height,
            connection_end.counterparty().prefix(),
            proof,
            connection_end.counterparty().connection_id(),
            expected_conn,
        )
        .map_err(error::verify_connection_state_error)
}

/// Verifies the client `proof` from a connection handshake message, typically from a
/// `MsgConnectionOpenTry` or a `MsgConnectionOpenAck`. The `expected_client_state` argument is a
/// representation for a client of the current chain (the chain handling the current message), which
/// is running on the counterparty chain (the chain which sent this message). This method does a
/// complete verification: that the client state the counterparty stores is valid (i.e., not frozen,
/// at the same revision as the current chain, with matching chain identifiers, etc) and that the
/// `proof` is correct.
pub fn verify_client_proof(
    ctx: &dyn ConnectionReader,
    connection_end: &ConnectionEnd,
    expected_client_state: AnyClientState,
    proof_height: Height,
    proof: &CommitmentProofBytes,
) -> Result<(), error::Error> {
    // Fetch the local client state (IBC client running on the host chain).
    let client_state = ctx
        .client_state(connection_end.client_id())
        .ok_or_else(|| error::missing_client_error(connection_end.client_id().clone()))?;

    if client_state.is_frozen() {
        return Err(error::frozen_client_error(
            connection_end.client_id().clone(),
        ));
    }

    let consensus_state = ctx
        .client_consensus_state(connection_end.client_id(), proof_height)
        .ok_or_else(|| {
            error::missing_client_consensus_state_error(
                proof_height,
                connection_end.client_id().clone(),
            )
        })?;

    let client_def = AnyClient::from_client_type(client_state.client_type());

    client_def
        .verify_client_full_state(
            &client_state,
            proof_height,
            consensus_state.root(),
            connection_end.counterparty().prefix(),
            connection_end.counterparty().client_id(),
            proof,
            &expected_client_state,
        )
        .map_err(|e| {
            error::client_state_verification_failure_error(connection_end.client_id().clone(), e)
        })
}

pub fn verify_consensus_proof(
    ctx: &dyn ConnectionReader,
    connection_end: &ConnectionEnd,
    proof_height: Height,
    proof: &ConsensusProof,
) -> Result<(), error::Error> {
    // Fetch the client state (IBC client on the local chain).
    let client_state = ctx
        .client_state(connection_end.client_id())
        .ok_or_else(|| error::missing_client_error(connection_end.client_id().clone()))?;

    if client_state.is_frozen() {
        return Err(error::frozen_client_error(
            connection_end.client_id().clone(),
        ));
    }

    // Fetch the expected consensus state from the historical (local) header data.
    let expected_consensus = ctx
        .host_consensus_state(proof.height())
        .ok_or_else(|| error::missing_local_consensus_state_error(proof.height()))?;

    let client = AnyClient::from_client_type(client_state.client_type());

    client
        .verify_client_consensus_state(
            &client_state,
            proof_height,
            connection_end.counterparty().prefix(),
            proof.proof(),
            connection_end.counterparty().client_id(),
            proof.height(),
            &expected_consensus,
        )
        .map_err(|e| error::consensus_state_verification_failure_error(proof.height(), e))
}

/// Checks that `claimed_height` is within normal bounds, i.e., fresh enough so that the chain has
/// not pruned it yet, but not newer than the current (actual) height of the local chain.
pub fn check_client_consensus_height(
    ctx: &dyn ConnectionReader,
    claimed_height: Height,
) -> Result<(), error::Error> {
    if claimed_height > ctx.host_current_height() {
        // Fail if the consensus height is too advanced.
        return Err(error::invalid_consensus_height_error(
            claimed_height,
            ctx.host_current_height(),
        ));
    }

    if claimed_height < ctx.host_oldest_height() {
        // Fail if the consensus height is too old (has been pruned).
        return Err(error::stale_consensus_height_error(
            claimed_height,
            ctx.host_oldest_height(),
        ));
    }

    // Height check is within normal bounds, check passes.
    Ok(())
}
