//! This module implements the protocol for ICS3, that is, the processing logic for ICS3
//! connection open handshake messages.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use crate::events::IBCEvent;
use crate::events::IBCEvent::{
    OpenAckConnection, OpenConfirmConnection, OpenInitConnection, OpenTryConnection,
};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::ctx::ICS3Context;
use crate::ics03_connection::error::Error;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics03_connection::msgs::ICS3Msg;

type ProtocolResult = Result<ProtocolOutput, Error>;

pub mod conn_open_ack;
pub mod conn_open_confirm;
pub mod conn_open_init;
pub mod conn_open_try;
pub mod verify;

#[derive(Debug, Clone, Default)]
pub struct ProtocolOutput {
    object: Option<Object>, // Vec<u8>? Data?
    events: Vec<IBCEvent>,
}

impl ProtocolOutput {
    pub fn new() -> ProtocolOutput {
        ProtocolOutput::default()
    }

    pub fn set_object(self, ce: ConnectionEnd) -> Self {
        Self {
            object: Some(ce),
            events: self.events,
        }
    }

    pub fn add_events(self, events: &mut Vec<IBCEvent>) -> Self {
        let mut evs = self.events.clone();
        evs.append(events);

        Self {
            events: evs,
            ..self
        }
    }
}

// The outcome after processing (delivering) a specific ICS3 message.
type Object = ConnectionEnd;

/// General entry point for delivering (i.e., processing) any type of message related to the ICS3
/// connection open handshake protocol.
pub fn process_ics3_msg(ctx: &dyn ICS3Context, message: &ICS3Msg) -> ProtocolResult {
    // Process each message with the corresponding process_*_msg function.
    // After processing a specific message, the output consists of a ConnectionEnd.
    let conn_object = match message {
        ICS3Msg::ConnectionOpenInit(msg) => conn_open_init::process(ctx, msg),
        ICS3Msg::ConnectionOpenTry(msg) => conn_open_try::process(ctx, msg),
        ICS3Msg::ConnectionOpenAck(msg) => conn_open_ack::process(ctx, msg),
        ICS3Msg::ConnectionOpenConfirm(msg) => conn_open_confirm::process(ctx, msg),
    }?;

    // Post-processing: emit events.
    let mut events = produce_events(ctx, message);

    Ok(ProtocolOutput::new()
        .set_object(conn_object)
        .add_events(&mut events))
}

/// Given a context and a message, produces the corresponding events.
pub fn produce_events(ctx: &dyn ICS3Context, msg: &ICS3Msg) -> Vec<IBCEvent> {
    let event = match msg {
        ICS3Msg::ConnectionOpenInit(msg) => OpenInitConnection(ConnectionEvents::OpenInit {
            height: ctx.chain_current_height(),
            connection_id: msg.connection_id().clone(),
            client_id: msg.client_id().clone(),
            counterparty_client_id: msg.counterparty().client_id().clone(),
        }),
        ICS3Msg::ConnectionOpenTry(msg) => OpenTryConnection(ConnectionEvents::OpenTry {
            height: ctx.chain_current_height(),
            connection_id: msg.connection_id().clone(),
            client_id: msg.client_id().clone(),
            counterparty_client_id: msg.counterparty().client_id().clone(),
        }),
        ICS3Msg::ConnectionOpenAck(msg) => OpenAckConnection(ConnectionEvents::OpenAck {
            height: ctx.chain_current_height(),
            connection_id: msg.connection_id().clone(),
        }),
        ICS3Msg::ConnectionOpenConfirm(msg) => {
            OpenConfirmConnection(ConnectionEvents::OpenConfirm {
                height: ctx.chain_current_height(),
                connection_id: msg.connection_id().clone(),
            })
        }
    };

    vec![event]
}
