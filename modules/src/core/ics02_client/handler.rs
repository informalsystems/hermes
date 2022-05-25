//! This module implements the processing logic for ICS2 (client abstractions and functions) msgs.
use crate::clients::host_functions::HostFunctionsProvider;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::msgs::ClientMsg;
use crate::core::ics26_routing::context::LightClientContext;
use crate::handler::HandlerOutput;
use core::fmt::Debug;

pub mod create_client;
pub mod update_client;
pub mod upgrade_client;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClientResult {
    Create(create_client::Result),
    Update(update_client::Result),
    Upgrade(upgrade_client::Result),
}

/// General entry point for processing any message related to ICS2 (client functions) protocols.
pub fn dispatch<Ctx, HostFunctions>(
    ctx: &Ctx,
    msg: ClientMsg,
) -> Result<HandlerOutput<ClientResult>, Error>
where
    Ctx: LightClientContext,
    HostFunctions: HostFunctionsProvider,
{
    match msg {
        ClientMsg::CreateClient(msg) => create_client::process(ctx, msg),
        ClientMsg::UpdateClient(msg) => update_client::process::<HostFunctions>(ctx, msg),
        ClientMsg::UpgradeClient(msg) => upgrade_client::process::<HostFunctions>(ctx, msg),
        _ => {
            unimplemented!()
        }
    }
}
