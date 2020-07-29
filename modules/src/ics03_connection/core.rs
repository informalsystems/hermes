//! This module implements the core functions of ICS03, that is, message processing logic for
//! processing any kind of ICS3 connection handshake message.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use std::collections::HashMap;

use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::exported::{get_compatible_versions, State};
use crate::ics03_connection::msgs::{
    ICS3Message, MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenInit,
    MsgConnectionOpenTry,
};
use crate::ics24_host::identifier::ConnectionId;

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
    // Fetch from the store the already existing  (if any) ConnectionEnd for this conn. identifier.
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

    provable_store.insert(conn_id.to_string(), new_ce);
    // TODO: insert corresponding association into the client namespace of privateStore.

    return Ok(());
}

/// Processing logic specific to messages of type `MsgConnectionOpenInit`.
fn process_init_msg(
    msg: MsgConnectionOpenInit,
    conn_end: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    if conn_end.is_some() {
        return Err(Kind::ConnectionExistsAlready
            .context(msg.connection_id().to_string())
            .into());
    }

    // TODO: consider adding `state` modifier to ConnectionEnd constructor.
    let mut connection_end = ConnectionEnd::new(
        msg.client_id().clone(),
        msg.counterparty().clone(),
        get_compatible_versions(),
    )?;

    connection_end.set_state(State::Init);

    return Ok(connection_end);
}

fn process_try_msg(
    _msg: MsgConnectionOpenTry,
    _conn_end: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    unimplemented!()
}

fn process_ack_msg(
    _msg: MsgConnectionOpenAck,
    _conn_end: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    unimplemented!()
}

fn process_confirm_msg(
    _msg: MsgConnectionOpenConfirm,
    _conn_end: Option<&ConnectionEnd>,
) -> Result<ConnectionEnd, Error> {
    unimplemented!()
}
