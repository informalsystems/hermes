use crate::handler::{Event, EventType, HandlerOutput};
use crate::ics02_client::error::Error;
use crate::ics02_client::msgs::ClientMsg;
use crate::ics24_host::identifier::ClientId;

use crate::ics02_client::context::{ClientKeeper, ClientReader};

pub mod create_client;
pub mod update_client;

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

pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: ClientMsg) -> Result<HandlerOutput<()>, Error>
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
