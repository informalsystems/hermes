//! This module implements the processing logic for ICS3 (connection open handshake) messages.

use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::Error;
use crate::ics03_connection::events::{
    ACK_EVENT_TYPE, CONFIRM_EVENT_TYPE, INIT_EVENT_TYPE, TRY_EVENT_TYPE,
};
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
    pub connection_id: Option<ConnectionId>,
    pub connection_end: ConnectionEnd,
}

impl From<ConnectionEvent> for Event {
    fn from(ev: ConnectionEvent) -> Event {
        match ev {
            ConnectionEvent::ConnOpenInit(_conn) => Event::new(
                EventType::Custom(INIT_EVENT_TYPE.to_string()),
                vec![("connection_id".to_string(), "None".to_string())],
            ),
            ConnectionEvent::ConnOpenTry(conn) => Event::new(
                EventType::Custom(TRY_EVENT_TYPE.to_string()),
                vec![(
                    "connection_id".to_string(),
                    // TODO: move connection id decision (`next_connection_id` method) in ClientReader
                    // to be able to write the connection identifier here, instead of the default.
                    conn.connection_id.unwrap_or_default().to_string(),
                )],
            ),
            ConnectionEvent::ConnOpenAck(conn) => Event::new(
                EventType::Custom(ACK_EVENT_TYPE.to_string()),
                vec![(
                    "connection_id".to_string(),
                    conn.connection_id.unwrap().to_string(),
                )],
            ),
            ConnectionEvent::ConnOpenConfirm(conn) => Event::new(
                EventType::Custom(CONFIRM_EVENT_TYPE.to_string()),
                vec![(
                    "connection_id".to_string(),
                    conn.connection_id.unwrap().to_string(),
                )],
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
    match msg {
        ConnectionMsg::ConnectionOpenInit(msg) => conn_open_init::process(ctx, msg),
        ConnectionMsg::ConnectionOpenTry(msg) => conn_open_try::process(ctx, *msg),
        ConnectionMsg::ConnectionOpenAck(msg) => conn_open_ack::process(ctx, *msg),
        ConnectionMsg::ConnectionOpenConfirm(msg) => conn_open_confirm::process(ctx, msg),
    }
}
