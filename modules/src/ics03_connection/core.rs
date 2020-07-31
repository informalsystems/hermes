//! This module implements the core functions of ICS03, that is, message processing logic for
//! processing any kind of ICS3 connection handshake message.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use crate::ics03_connection::connection::{ConnectionEnd, Counterparty};
use crate::ics03_connection::ctx::ICS3Context;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::exported::{get_compatible_versions, pick_version, State};
use crate::ics03_connection::msgs::{
    ICS3Msg, MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenInit,
    MsgConnectionOpenTry,
};
use crate::ics24_host::introspect::{current_height, get_commitment_prefix, trusting_period};
use crate::proofs::Proofs;
use crate::Height;

/// General entry point for processing any type of message related to the ICS03 connection open
/// handshake protocol.
/// The `provable_store` parameter is a basic workaround, since there is no KV store yet.
/// TODO: the provable_store should be abstracted over, e.g., with a Keeper or similar mechanism.
pub fn process_conn_open_msg(ctx: &ICS3Context, message: ICS3Msg) -> Result<(), Error> {
    // Process each message with the corresponding process_*_msg function.
    // After processing a specific message, the output consists of a ConnectionEnd, i.e., an updated
    // version of the `current_conn_end` that should be updated in the provable store.
    let _new_ce = match message {
        ICS3Msg::ConnectionOpenInit(msg) => process_init_msg(ctx, msg),
        ICS3Msg::ConnectionOpenTry(msg) => process_try_msg(ctx, msg),
        ICS3Msg::ConnectionOpenAck(msg) => process_ack_msg(ctx, msg),
        ICS3Msg::ConnectionOpenConfirm(msg) => process_confirm_msg(ctx, msg),
    }?;

    // Post-processing?

    Ok(())
}

/// Processing logic specific to messages of type `MsgConnectionOpenInit`.
fn process_init_msg(ctx: &ICS3Context, msg: MsgConnectionOpenInit) -> Result<ConnectionEnd, Error> {
    // No connection should exist.
    if ctx.current_connection().is_some() {
        Err(Kind::ConnectionExistsAlready
            .context(msg.connection_id().to_string())
            .into())
    } else {
        let mut connection_end = ConnectionEnd::new(
            msg.client_id().clone(),
            msg.counterparty().clone(),
            get_compatible_versions(),
        )?;
        connection_end.set_state(State::Init);

        Ok(connection_end)
    }
}

fn process_try_msg(ctx: &ICS3Context, msg: MsgConnectionOpenTry) -> Result<ConnectionEnd, Error> {
    // Check that consensus height (for client proof) in message is not too advanced nor too old.
    check_client_consensus_height(msg.consensus_height())?;

    // Proof verification in two steps:
    // 1. Setup: build the ConnectionEnd as we expect to find it on the other party.
    let mut expected_conn = ConnectionEnd::new(
        msg.counterparty().client_id().clone(),
        Counterparty::new(
            msg.client_id().as_str().into(),
            msg.connection_id().as_str().into(),
            get_commitment_prefix(),
        )?,
        msg.counterparty_versions(),
    )?;
    expected_conn.set_state(State::Init);
    // 2. Pass the details to our verification function.
    verify_proofs(expected_conn, msg.proofs())?;

    // Unwrap the old connection end (if any) and validate it against the message.
    let mut new_ce = match ctx.current_connection() {
        Some(old_conn_end) => {
            // Validate that existing connection end matches with the one we're trying to establish.
            if old_conn_end.state_matches(&State::Init)
                && old_conn_end.counterparty_matches(&msg.counterparty())
                && old_conn_end.client_id_matches(msg.client_id())
            {
                // A ConnectionEnd already exists and all validation passed.
                Ok(old_conn_end.clone())
            } else {
                // A ConnectionEnd already exists and validation failed.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch.context(msg.connection_id().to_string()),
                ))
            }
        }
        // No ConnectionEnd exists for this ConnectionId. Create & return a new one.
        None => Ok(ConnectionEnd::new(
            msg.client_id().clone(),
            msg.counterparty().clone(),
            msg.counterparty_versions(),
        )?),
    }?;

    // Transition the connection end to the new state & pick a version.
    new_ce.set_state(State::TryOpen);
    new_ce.set_version(pick_version(msg.counterparty_versions()).unwrap());
    // TODO: fix version.
    Ok(new_ce)
}

fn process_ack_msg(ctx: &ICS3Context, msg: MsgConnectionOpenAck) -> Result<ConnectionEnd, Error> {
    // Check the client's (consensus state) proof height.
    check_client_consensus_height(msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn_end = match ctx.current_connection() {
        // A connection end must exist and must be Init or TryOpen; otherwise we return an error.
        Some(old_conn_end) => {
            if !(old_conn_end.state_matches(&State::Init)
                || old_conn_end.state_matches(&State::TryOpen))
            {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch.context(msg.connection_id().to_string()),
                ))
            } else {
                Ok(old_conn_end.clone())
            }
        }
        None => {
            // No connection end exists for this conn. identifier. Impossible to continue handshake.
            Err(Into::<Error>::into(
                Kind::UninitializedConnection.context(msg.connection_id().to_string()),
            ))
        }
    }?;

    // Proof verification.
    let mut versions: Vec<String> = Vec::with_capacity(1); // Workaround for versions (constructor expects vector).
    versions.push(msg.version().clone());
    let mut expected_conn = ConnectionEnd::new(
        new_conn_end.counterparty().client_id().clone(),
        Counterparty::new(
            // The counterparty is The local chain.
            new_conn_end.client_id(), // The local client identifier.
            msg.connection_id().as_str().into(), // Local connection id.
            get_commitment_prefix(),  // Local commitment prefix.
        )?,
        versions,
    )?;
    expected_conn.set_state(State::TryOpen);
    // 2. Pass the details to our verification function.
    verify_proofs(expected_conn, msg.proofs())?;

    new_conn_end.set_state(State::Open);
    new_conn_end.set_version(msg.version().clone());
    Ok(new_conn_end)
}

fn process_confirm_msg(
    ctx: &ICS3Context,
    msg: MsgConnectionOpenConfirm,
) -> Result<ConnectionEnd, Error> {
    // Unwrap the old connection end & validate it.
    let mut new_conn_end = match ctx.current_connection() {
        // A connection end must exist and must be in TryOpen state; otherwise return error.
        Some(old_conn_end) => {
            if !(old_conn_end.state_matches(&State::TryOpen)) {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch.context(msg.connection_id().to_string()),
                ))
            } else {
                Ok(old_conn_end.clone())
            }
        }
        None => {
            // No connection end exists for this conn. identifier. Impossible to continue handshake.
            Err(Into::<Error>::into(
                Kind::UninitializedConnection.context(msg.connection_id().to_string()),
            ))
        }
    }?;

    // Verify proofs.
    let mut expected_conn = ConnectionEnd::new(
        new_conn_end.counterparty().client_id().clone(),
        Counterparty::new(
            // The counterparty is the local chain.
            new_conn_end.client_id(), // The local client identifier.
            msg.connection_id().as_str().into(), // Local connection id.
            get_commitment_prefix(),  // Local commitment prefix.
        )?,
        new_conn_end.versions(),
    )?;
    expected_conn.set_state(State::Open);
    // 2. Pass the details to our verification function.
    verify_proofs(expected_conn, msg.proofs())?;

    new_conn_end.set_state(State::Open);
    Ok(new_conn_end)
}

fn verify_proofs(_expected_conn: ConnectionEnd, _proofs: &Proofs) -> Result<(), Error> {
    unimplemented!()
    // Authenticity and semantic (validity checks), roughly speaking:
    // - client consensus state (must match our own state for the given height)
    // - connection state (must match _expected_conn)
}

fn check_client_consensus_height(claimed_height: Height) -> Result<(), Error> {
    if claimed_height > current_height() {
        // Fail if the consensus height is too advanced.
        Err(Kind::InvalidConsensusHeight
            .context(claimed_height.to_string())
            .into())
    } else if claimed_height < (current_height() - trusting_period()) {
        // Fail if the consensus height is too old (outside of trusting period).
        Err(Kind::StaleConsensusHeight
            .context(claimed_height.to_string())
            .into())
    } else {
        Ok(())
    }
}
