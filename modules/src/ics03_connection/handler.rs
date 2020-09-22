//! This module implements the the processing logic for ICS3 (connection open handshake) messages.
use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::Error;
use crate::ics03_connection::msgs::ConnectionMsg;
use crate::ics24_host::identifier::ConnectionId;

pub mod conn_open_ack;
pub mod conn_open_confirm;
pub mod conn_open_init;
pub mod conn_open_try;
pub mod verify;

#[derive(Clone, Debug)]
pub struct ConnectionResult {
    connection_id: ConnectionId,
    connection_end: ConnectionEnd,
}

#[derive(Clone, Debug)]
pub enum ConnectionEvent {
    ConnOpenInit(ConnectionResult),
    ConnOpenTry(ConnectionResult),
    ConnOpenAck(ConnectionResult),
    ConnOpenConfirm(ConnectionResult),
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

// The outcome after processing (delivering) a specific ICS3 message.
type Object = ConnectionEnd;

/// General entry point for processing any type of message related to the ICS3 connection open
/// handshake protocol.
pub fn dispatch<Ctx>(
    ctx: &mut Ctx,
    msg: ConnectionMsg,
) -> Result<HandlerOutput<ConnectionResult>, Error>
where
    Ctx: ConnectionReader + ConnectionKeeper,
{
    // TODO: generalize this to reduce duplicate code across the match arms.
    match msg {
        ConnectionMsg::ConnectionOpenInit(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = conn_open_init::process(ctx, msg)?;

            conn_open_init::keep(ctx, result.clone())?;
            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(result))
        }
        ConnectionMsg::ConnectionOpenTry(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = conn_open_try::process(ctx, *msg)?;

            conn_open_try::keep(ctx, result.clone())?;
            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(result))
        }
        ConnectionMsg::ConnectionOpenAck(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = conn_open_ack::process(ctx, msg)?;

            conn_open_ack::keep(ctx, result.clone())?;
            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(result))
        }
        ConnectionMsg::ConnectionOpenConfirm(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = conn_open_confirm::process(ctx, msg)?;

            conn_open_confirm::keep(ctx, result.clone())?;
            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(result))
        }
    }
}
