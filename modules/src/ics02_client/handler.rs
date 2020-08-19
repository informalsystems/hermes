#![allow(unused_imports)]

use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics02_client::client_def::{AnyClient, AnyClientState, AnyConsensusState, ClientDef};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics02_client::msgs::{MsgCreateAnyClient, MsgUpdateAnyClient};
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics24_host::identifier::ClientId;

use crate::Height;

pub mod create_client;
pub mod update_client;

pub trait ClientReader {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;
    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState>;
}

pub trait ClientKeeper {
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Error>;

    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: AnyClientState,
    ) -> Result<(), Error>;

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        consensus_state: AnyConsensusState,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClientEvent {
    ClientCreated(ClientId),
    ClientUpdated(ClientId),
}

impl From<ClientEvent> for Event {
    fn from(ce: ClientEvent) -> Event {
        match ce {
            ClientEvent::ClientCreated(client_id) => Event::new(
                EventType::Custom("ClientCreated".to_string()),
                vec![("client_id".to_string(), client_id.to_string())],
            ),
            ClientEvent::ClientUpdated(client_id) => Event::new(
                EventType::Custom("ClientUpdated".to_string()),
                vec![("client_id".to_string(), client_id.to_string())],
            ),
        }
    }
}

pub enum ClientMsg<CD: ClientDef> {
    CreateClient(MsgCreateAnyClient<CD>),
    UpdateClient(MsgUpdateAnyClient<CD>),
}

pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: ClientMsg<AnyClient>) -> Result<HandlerOutput<()>, Error>
where
    Ctx: ClientReader + ClientKeeper,
{
    match msg {
        ClientMsg::CreateClient(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = create_client::process(ctx, msg)?;

            create_client::keep(ctx, result)?;

            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(()))
        }
        ClientMsg::UpdateClient(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = update_client::process(ctx, msg)?;

            update_client::keep(ctx, result)?;

            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(()))
        }
    }
}
