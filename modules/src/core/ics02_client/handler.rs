//! This module implements the processing logic for ICS2 (client abstractions and functions) msgs.

use crate::core::ics02_client::context::ClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::msgs::ClientMsg;
use crate::handler::HandlerOutput;

pub mod create_client;
pub mod update_client;
pub mod upgrade_client;

#[derive(Clone, Debug, PartialEq)]
pub enum ClientResult {
    Create(create_client::Result),
    Update(update_client::Result),
    Upgrade(upgrade_client::Result),
}

/// General entry point for processing any message related to ICS2 (client functions) protocols.
pub fn dispatch<Ctx>(ctx: &Ctx, msg: ClientMsg) -> Result<HandlerOutput<ClientResult>, Error>
where
    Ctx: ClientReader,
{
    match msg {
        ClientMsg::CreateClient(msg) => create_client::process(ctx, msg),
        ClientMsg::UpdateClient(msg) => update_client::process(ctx, msg),
        ClientMsg::UpgradeClient(msg) => upgrade_client::process(ctx, msg),
        _ => {
            unimplemented!()
        }
    }
}
