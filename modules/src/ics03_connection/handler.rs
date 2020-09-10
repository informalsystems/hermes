//! This module implements the protocol for ICS3, that is, the processing logic for ICS3
//! connection open handshake messages.
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
        }
    }
}

// The outcome after processing (delivering) a specific ICS3 message.
type Object = ConnectionEnd;

/// General entry point for delivering (i.e., processing) any type of message related to the ICS3
/// connection open handshake protocol.
// pub fn process_ics3_msg(ctx: &dyn ConnectionReader, message: &ConnectionMsg) -> ProtocolResult {
//     // Process each message with the corresponding process_*_msg function.
//     // After processing a specific message, the output consists of a ConnectionEnd.
//     let conn_object = match message {
//         ConnectionMsg::ConnectionOpenInit(msg) => conn_open_init::process(ctx, msg),
//         ConnectionMsg::ConnectionOpenTry(msg) => conn_open_try::process(ctx, msg),
//         ConnectionMsg::ConnectionOpenAck(msg) => conn_open_ack::process(ctx, msg),
//         ConnectionMsg::ConnectionOpenConfirm(msg) => conn_open_confirm::process(ctx, msg),
//     }?;
//
//     // Post-processing: emit events.
//     let mut events = produce_events(ctx, message);
//
//     Ok(ProtocolOutput::new()
//         .set_object(conn_object)
//         .add_events(&mut events))
// }

pub fn keep(keeper: &mut dyn ConnectionKeeper, result: ConnectionResult) -> Result<(), Error> {
    keeper.store_connection(&result.connection_id, &result.connection_end)?;
    keeper.store_connection_to_client(&result.connection_id, &result.connection_end.client_id())?;
    Ok(())
}

pub fn dispatch<Ctx>(
    ctx: &mut Ctx,
    msg: ConnectionMsg,
) -> Result<HandlerOutput<ConnectionResult>, Error>
where
    Ctx: ConnectionReader + ConnectionKeeper,
{
    match msg {
        ConnectionMsg::ConnectionOpenInit(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = conn_open_init::process(ctx, msg)?;

            keep(ctx, result.clone())?;
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
            } = conn_open_try::process(ctx, msg)?;

            keep(ctx, result.clone())?;
            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(result))
        }
    }
}
