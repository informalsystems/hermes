//! This module implements the core functions of ICS03, that is, message processing logic for
//! processing any kind of ICS3 connection handshake message.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use std::collections::HashMap;

use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::exported::{get_compatible_versions, pick_version, Connection, State};
use crate::ics03_connection::msgs::{
    ICS3Message, MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenInit,
    MsgConnectionOpenTry,
};
use crate::ics24_host::identifier::ConnectionId;
use crate::ics24_host::introspect::{current_height, trusting_period};

/// General entry point for processing any type of message related to the ICS03 connection open
/// handshake protocol.
/// The `provable_store` parameter is a basic workaround, since there is no KV store yet.
/// TODO: the provable_store should be abstracted over, e.g., with a Keeper or similar mechanism.
pub fn process_conn_open_handshake_msg(
    message: ICS3Message,
    conn_id: &ConnectionId,
    provable_store: &mut HashMap<String, ConnectionEnd>,
) -> Result<(), Error> {
    // Preprocessing of the message. Basic validation was done already when creating the msg.
    // Fetch from the store the already existing (if any) ConnectionEnd for this conn. identifier.
    let current_conn_end = provable_store.get(conn_id.as_str());

    // Process each message with the corresponding process_*_msg function.
    // After processing a specific message, the outcome consists of a write set, i.e., a list of
    // <key,value> pairs that must be updated in the provable store.
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
    // Fail-fast if the consensus height in the message is too advanced.
    if msg.consensus_height() > current_height() {
        return Err(Kind::InvalidConsensusHeight
            .context(msg.consensus_height().to_string())
            .into());
    }
    // Fail if the consensus height in the message is too old (outside of trusting period).
    if msg.consensus_height() < (current_height() - trusting_period()) {
        return Err(Kind::StaleConsensusHeight
            .context(msg.consensus_height().to_string())
            .into());
    }
    // Verify if the existing connection end matches with the one we're trying to establish.
    match opt_conn {
        Some(old_conn_end) => {
            if old_conn_end.state_matches(&State::Init)
                && old_conn_end.counterparty_matches(&msg.counterparty())
                && old_conn_end.client_id_matches(msg.client_id())
            {
                // A ConnectionEnd already exists and all verification passed.
                // Transition to state TryOpen.
                let mut new_conn = old_conn_end.clone();
                new_conn.set_state(State::TryOpen);
                // TODO: fix version.
                new_conn.set_version(pick_version(old_conn_end.versions()).unwrap());
                Ok(new_conn)
            } else {
                // A ConnectionEnd already exists and verification failed.
                Err(Kind::ConnectionMismatch
                    .context(msg.consensus_height().to_string())
                    .into())
            }
        }
        // No ConnectionEnd exists for this ConnectionId. Create & return a new one.
        None => {
            let mut connection_end = ConnectionEnd::new(
                msg.client_id().clone(),
                msg.counterparty().clone(),
                get_compatible_versions(),
            )?;
            connection_end.set_state(State::TryOpen);

            return Ok(connection_end);
        }
    }
}

fn process_ack_msg(
    _msg: MsgConnectionOpenAck,
    _opt_conn: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    unimplemented!()
}

fn process_confirm_msg(
    _msg: MsgConnectionOpenConfirm,
    _opt_conn: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    unimplemented!()
}
