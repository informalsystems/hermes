//! This module implements the processing logic for ICS2 (client abstractions and functions) msgs.

use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics02_client::error::Error;
use crate::ics02_client::msgs::ClientMsg;
use crate::ics24_host::identifier::ClientId;

use crate::ics02_client::context::ClientReader;
use crate::ics02_client::handler::create_client as ics2_create_client;
use crate::ics02_client::handler::update_client as ics2_update_client;

pub mod create_client;
pub mod update_client;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClientEvent {
    Created(ClientId),
    Updated(ClientId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClientResult {
    Create(ics2_create_client::Result),
    Update(ics2_update_client::Result),
}

impl From<ClientEvent> for Event {
    fn from(ce: ClientEvent) -> Event {
        match ce {
            ClientEvent::Created(client_id) => Event::new(
                EventType::Custom("ClientCreated".to_string()),
                vec![("client_id".to_string(), client_id.to_string())],
            ),
            ClientEvent::Updated(client_id) => Event::new(
                EventType::Custom("ClientUpdated".to_string()),
                vec![("client_id".to_string(), client_id.to_string())],
            ),
        }
    }
}

/// General entry point for processing any message related to ICS2 (client functions) protocols.
pub fn dispatch<Ctx>(ctx: &Ctx, msg: ClientMsg) -> Result<HandlerOutput<ClientResult>, Error>
where
    Ctx: ClientReader,
{
    Ok(match msg {
        ClientMsg::CreateClient(msg) => ics2_create_client::process(ctx, msg)?,
        ClientMsg::UpdateClient(msg) => ics2_update_client::process(ctx, msg)?,
    })
}
