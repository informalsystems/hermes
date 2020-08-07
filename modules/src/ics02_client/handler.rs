use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics02_client::client::ClientDef;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics02_client::msgs::MsgCreateClient;
use crate::ics24_host::identifier::ClientId;

use crate::Height;

pub mod create_client;
// pub mod update_client;

pub trait ClientContext<CD>
where
    CD: ClientDef,
{
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: &ClientId) -> Option<CD::ClientState>;
    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<CD::ConsensusState>;
}

pub trait ClientKeeper<CD: ClientDef> {
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Error>;

    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: CD::ClientState,
    ) -> Result<(), Error>;

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        consensus_state: CD::ConsensusState,
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
    CreateClient(MsgCreateClient<CD>),
    // UpdateClient(UpdateClientMsg<CD>),
}

pub fn handler<CD, Ctx>(ctx: &mut Ctx, msg: ClientMsg<CD>) -> Result<HandlerOutput<()>, Error>
where
    CD: ClientDef,
    Ctx: ClientContext<CD> + ClientKeeper<CD>,
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
    }
}

