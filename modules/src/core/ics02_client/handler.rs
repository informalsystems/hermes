//! This module implements the processing logic for ICS2 (client abstractions and functions) msgs.
use crate::clients::crypto_ops::crypto::CryptoOps;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::msgs::ClientMsg;
use crate::core::ics26_routing::context::LightClientContext;
use crate::handler::HandlerOutput;
use core::fmt::Debug;

pub mod create_client;
pub mod update_client;
pub mod upgrade_client;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClientResult<Crypto> {
    Create(create_client::Result<Crypto>),
    Update(update_client::Result<Crypto>),
    Upgrade(upgrade_client::Result<Crypto>),
}

/// General entry point for processing any message related to ICS2 (client functions) protocols.
pub fn dispatch<Ctx, Crypto>(
    ctx: &Ctx,
    msg: ClientMsg<Crypto>,
) -> Result<HandlerOutput<ClientResult<Crypto>>, Error>
where
    Ctx: LightClientContext<Crypto = Crypto>,
    Crypto: CryptoOps + Debug + Send + Sync + PartialEq + Eq,
{
    match msg {
        ClientMsg::CreateClient(msg) => create_client::process::<Crypto>(ctx, msg),
        ClientMsg::UpdateClient(msg) => update_client::process::<Crypto>(ctx, msg),
        ClientMsg::UpgradeClient(msg) => upgrade_client::process::<Crypto>(ctx, msg),
        _ => {
            unimplemented!()
        }
    }
}
