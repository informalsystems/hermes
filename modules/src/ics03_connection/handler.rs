//! This module implements the processing logic for ICS3 (connection open handshake) messages.

use crate::handler::HandlerOutput;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::Error;
use crate::ics03_connection::msgs::ConnectionMsg;
use crate::ics24_host::identifier::ConnectionId;

pub mod conn_open_ack;
pub mod conn_open_confirm;
pub mod conn_open_init;
pub mod conn_open_try;
mod verify;

#[derive(Clone, Debug)]
pub struct ConnectionResult {
    pub connection_id: Option<ConnectionId>,
    pub connection_end: ConnectionEnd,
}

/// General entry point for processing any type of message related to the ICS3 connection open
/// handshake protocol.
pub fn dispatch<Ctx>(
    ctx: &Ctx,
    msg: ConnectionMsg,
) -> Result<HandlerOutput<ConnectionResult>, Error>
where
    Ctx: ConnectionReader,
{
    match msg {
        ConnectionMsg::ConnectionOpenInit(msg) => conn_open_init::process(ctx, msg),
        ConnectionMsg::ConnectionOpenTry(msg) => conn_open_try::process(ctx, *msg),
        ConnectionMsg::ConnectionOpenAck(msg) => conn_open_ack::process(ctx, *msg),
        ConnectionMsg::ConnectionOpenConfirm(msg) => conn_open_confirm::process(ctx, msg),
    }
}
