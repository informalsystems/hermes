//! This module implements the core functions of ICS03, that is, message processing logic for
//! processing any kind of ICS3 connection handshake message.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use std::collections::HashMap;

use crate::ics03_connection::connection::{ConnectionEnd, Counterparty};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::exported::{get_compatible_versions, pick_version, State};
use crate::ics03_connection::msgs::{
    ICS3Message, MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenInit,
    MsgConnectionOpenTry,
};
use crate::ics24_host::identifier::ConnectionId;
use crate::ics24_host::introspect::{current_height, get_commitment_prefix, trusting_period};
use crate::proofs::Proofs;
use crate::Height;

/// General entry point for processing any type of message related to the ICS03 connection open
/// handshake protocol.
/// The `provable_store` parameter is a basic workaround, since there is no KV store yet.
/// TODO: the provable_store should be abstracted over, e.g., with a Keeper or similar mechanism.
pub fn process_conn_open_handshake_msg(
    message: ICS3Message,
    conn_id: &ConnectionId,
    provable_store: &mut HashMap<String, ConnectionEnd>,
) -> Result<(), Error> {
    // Preprocessing. Basic validation of `message` was done already when creating it.
    // Fetch from the store the already existing (if any) ConnectionEnd for this conn. identifier.
    let current_conn_end = provable_store.get(conn_id.as_str());

    // Process each message with the corresponding process_*_msg function.
    // After processing a specific message, the output consists of a ConnectionEnd, i.e., an updated
    // version of the `current_conn_end` that should be updated in the provable store.
    let new_ce = match message {
        ICS3Message::ConnectionOpenInit(msg) => process_init_msg(msg, current_conn_end),
        ICS3Message::ConnectionOpenTry(msg) => process_try_msg(msg, current_conn_end),
        ICS3Message::ConnectionOpenAck(msg) => process_ack_msg(msg, current_conn_end),
        ICS3Message::ConnectionOpenConfirm(msg) => process_confirm_msg(msg, current_conn_end),
    }?;

    // Post-processing.
    provable_store.insert(conn_id.to_string(), new_ce);
    // TODO: insert corresponding association into the /clients namespace of privateStore.

    Ok(())
}

/// Processing logic specific to messages of type `MsgConnectionOpenInit`.
fn process_init_msg(
    msg: MsgConnectionOpenInit,
    opt_conn: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    // No connection should exist.
    if opt_conn.is_some() {
        return Err(Kind::ConnectionExistsAlready
            .context(msg.connection_id().to_string())
            .into());
    }

    let mut connection_end = ConnectionEnd::new(
        msg.client_id().clone(),
        msg.counterparty().clone(),
        get_compatible_versions(),
    )?;

    connection_end.set_state(State::Init);

    return Ok(connection_end);
}

fn process_try_msg(
    msg: MsgConnectionOpenTry,
    opt_conn: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
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
    let mut new_ce = match opt_conn {
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

fn process_ack_msg(
    msg: MsgConnectionOpenAck,
    opt_conn: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    // Check the client's (consensus state) proof height.
    check_client_consensus_height(msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn_end = match opt_conn {
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
    let mut versions:Vec<String> = Vec::with_capacity(1);   // Workaround for versions (constructor expects vector).
    versions.push(msg.version().clone());
    let mut expected_conn = ConnectionEnd::new(
        new_conn_end.counterparty().client_id().clone(),
        Counterparty::new( // the counterparty is the local chain.
            new_conn_end.client_id(),   // the local client identifier.
            msg.connection_id().as_str().into(), // local connection id.
            get_commitment_prefix(), // local commitment prefix.
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
    _msg: MsgConnectionOpenConfirm,
    _opt_conn: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    unimplemented!()
}

fn verify_proofs(_expected_conn: ConnectionEnd, _proofs: &Proofs) -> Result<(), Error> {
    unimplemented!()
    // Authenticity and semantic (validity checks), roughly speaking:
    // - client consensus state (must match our own state for the given height)
    // - connection state (must match _expected_conn)
}

fn check_client_consensus_height(reported_height: Height) -> Result<(), Error> {
    if reported_height > current_height() {
        // Fail if the consensus height in the message is too advanced.
        Err(Kind::InvalidConsensusHeight
            .context(reported_height.to_string())
            .into())
    } else if reported_height < (current_height() - trusting_period()) {
        // Fail if the consensus height in the message is too old (outside of trusting period).
        Err(Kind::StaleConsensusHeight
            .context(reported_height.to_string())
            .into())
    } else {
        Ok(())
    }
}
