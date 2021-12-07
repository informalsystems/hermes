//! ICS3 verification functions, common across all four handlers of ICS3.

use crate::core::ics02_client::client_consensus::ConsensusState;
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics03_connection::context::ConnectionReader;
use crate::core::ics03_connection::error::Error;
use crate::core::ics24_host::Path;
use crate::proofs::Proofs;
use crate::Height;

/// Entry point for verifying all proofs bundled in any ICS3 message.
pub fn verify_proofs(
    ctx: &dyn ConnectionReader,
    client_state: Option<AnyClientState>,
    connection_end: &ConnectionEnd,
    expected_conn: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    verify_connection_proof(ctx, connection_end, expected_conn, proofs)?;

    // If the message includes a client state, then verify the proof for that state.
    if let Some(expected_client_state) = client_state {
        verify_client_proof(ctx, connection_end, expected_client_state, proofs)?;
    }

    verify_consensus_proof(ctx, connection_end, proofs)
}

/// Verifies the authenticity and semantic correctness of a commitment `proof`. The commitment
/// claims to prove that an object of type connection exists on the source chain (i.e., the chain
/// which created this proof). This object must match the state of `expected_conn`.
pub fn verify_connection_proof(
    ctx: &dyn ConnectionReader,
    connection_end: &ConnectionEnd,
    expected_conn: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    // Fetch the client state (IBC client on the local/host chain).
    let client_state = ctx.client_state(connection_end.client_id())?;

    // The client must have the consensus state for the height where this proof was created.
    let consensus_state =
        ctx.client_consensus_state(connection_end.client_id(), proofs.height())?;

    // A counterparty connection id of None causes `unwrap()` below and indicates an internal
    // error as this is the connection id on the counterparty chain that must always be present.
    let connection_id = connection_end
        .counterparty()
        .connection_id()
        .ok_or_else(Error::invalid_counterparty)?;
    let path = Path::Connections(connection_id.clone());

    let client_def = AnyClient::from_client_type(client_state.client_type());

    // Verify the proof for the connection state against the expected connection end.
    client_def
        .verify_connection_state(
            &client_state,
            connection_end.counterparty().prefix(),
            proofs,
            consensus_state.root(),
            &path,
            expected_conn,
        )
        .map_err(Error::verify_connection_state)
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
    proofs: &Proofs,
) -> Result<(), Error> {
    let client_id = connection_end.client_id();
    let path = Path::ClientState(client_id.clone());

    // Fetch the local client state (IBC client running on the host chain).
    let client_state = ctx.client_state(client_id)?;

    let consensus_state = ctx.client_consensus_state(client_id, proofs.height())?;

    let client_def = AnyClient::from_client_type(client_state.client_type());

    client_def
        .verify_client_full_state(
            &client_state,
            connection_end.counterparty().prefix(),
            proofs,
            consensus_state.root(),
            &path,
            &expected_client_state,
        )
        .map_err(|e| {
            Error::client_state_verification_failure(connection_end.client_id().clone(), e)
        })
}

pub fn verify_consensus_proof(
    ctx: &dyn ConnectionReader,
    connection_end: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    // If a consensus proof is attached to the message, then verify it.
    let consensus_height = match proofs.consensus_proof() {
        Some(consensus_proof) => consensus_proof.height(),
        None => return Ok(()),
    };

    let client_id = connection_end.client_id();
    let path = Path::ClientConsensusState {
        client_id: client_id.clone(),
        epoch: consensus_height.revision_number,
        height: consensus_height.revision_height,
    };

    // Fetch the client state (IBC client on the local chain).
    let client_state = ctx.client_state(client_id)?;

    // Fetch the expected consensus state from the historical (local) header data.
    let expected_consensus = ctx.host_consensus_state(consensus_height)?;

    let client = AnyClient::from_client_type(client_state.client_type());

    client
        .verify_client_consensus_state(
            &client_state,
            connection_end.counterparty().prefix(),
            proofs,
            expected_consensus.root(),
            &path,
            &expected_consensus,
        )
        .map_err(|e| Error::consensus_state_verification_failure(consensus_height, e))
}

/// Checks that `claimed_height` is within normal bounds, i.e., fresh enough so that the chain has
/// not pruned it yet, but not newer than the current (actual) height of the local chain.
pub fn check_client_consensus_height(
    ctx: &dyn ConnectionReader,
    claimed_height: Height,
) -> Result<(), Error> {
    if claimed_height > ctx.host_current_height() {
        // Fail if the consensus height is too advanced.
        return Err(Error::invalid_consensus_height(
            claimed_height,
            ctx.host_current_height(),
        ));
    }

    if claimed_height < ctx.host_oldest_height() {
        // Fail if the consensus height is too old (has been pruned).
        return Err(Error::stale_consensus_height(
            claimed_height,
            ctx.host_oldest_height(),
        ));
    }

    // Height check is within normal bounds, check passes.
    Ok(())
}
