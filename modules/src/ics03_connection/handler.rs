//! This module implements the processing logic for ICS3 (connection open handshake) messages.

use crate::handler::{Event, EventType, HandlerOutput};
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
pub enum ConnectionEvent {
    ConnOpenInit(ConnectionResult),
    ConnOpenTry(ConnectionResult),
    ConnOpenAck(ConnectionResult),
    ConnOpenConfirm(ConnectionResult),
}

#[derive(Clone, Debug)]
pub struct ConnectionResult {
    pub connection_id: ConnectionId,
    pub connection_end: ConnectionEnd,
}

impl From<ConnectionEvent> for Event {
    fn from(ev: ConnectionEvent) -> Event {
        match ev {
            ConnectionEvent::ConnOpenInit(conn) => Event::new(
                EventType::Custom("connection_open_init".to_string()),
                vec![("connection_id".to_string(), conn.connection_id.to_string())],
            ),
            ConnectionEvent::ConnOpenTry(conn) => Event::new(
                EventType::Custom("connection_open_try".to_string()),
                vec![("connection_id".to_string(), conn.connection_id.to_string())],
            ),
            ConnectionEvent::ConnOpenAck(conn) => Event::new(
                EventType::Custom("connection_open_ack".to_string()),
                vec![("connection_id".to_string(), conn.connection_id.to_string())],
            ),
            ConnectionEvent::ConnOpenConfirm(conn) => Event::new(
                EventType::Custom("connection_open_confirm".to_string()),
                vec![("connection_id".to_string(), conn.connection_id.to_string())],
            ),
        }
    }
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
    Ok(match msg {
        ConnectionMsg::ConnectionOpenInit(msg) => conn_open_init::process(ctx, msg)?,
        ConnectionMsg::ConnectionOpenTry(msg) => conn_open_try::process(ctx, *msg)?,
        ConnectionMsg::ConnectionOpenAck(msg) => conn_open_ack::process(ctx, *msg)?,
        ConnectionMsg::ConnectionOpenConfirm(msg) => conn_open_confirm::process(ctx, msg)?,
    })
}
