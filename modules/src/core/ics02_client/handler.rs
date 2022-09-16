//! This module implements the processing logic for ICS2 (client abstractions and functions) msgs.

use crate::{
	core::{
		ics02_client::{context::ClientKeeper, error::Error, msgs::ClientMsg},
		ics26_routing::context::ReaderContext,
	},
	handler::HandlerOutput,
};
use core::fmt::Debug;

pub mod create_client;
pub mod update_client;
pub mod upgrade_client;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClientResult<C: ClientKeeper> {
	Create(create_client::Result<C>),
	Update(update_client::Result<C>),
	Upgrade(upgrade_client::Result<C>),
}

/// General entry point for processing any message related to ICS2 (client functions) protocols.
pub fn dispatch<Ctx>(
	ctx: &Ctx,
	msg: ClientMsg<Ctx>,
) -> Result<HandlerOutput<ClientResult<Ctx>>, Error>
where
	Ctx: ReaderContext,
{
	match msg {
		ClientMsg::CreateClient(msg) => create_client::process::<_>(ctx, msg),
		ClientMsg::UpdateClient(msg) => update_client::process::<_>(ctx, msg),
		ClientMsg::UpgradeClient(msg) => upgrade_client::process::<_>(ctx, msg),
		_ => {
			unimplemented!()
		},
	}
}
