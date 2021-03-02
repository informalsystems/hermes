//! This module implements the processing logic for ICS20 (token transfer) message.

use crate::application::ics20_fungible_token_transfer::context::Ics20Context;
use crate::handler::HandlerOutput;
use crate::ics04_channel::packet::PacketResult;

use super::error::{Error, Kind};
use super::msgs::transfer::MsgTransfer;
use super::relay_application_logic;

pub mod send_transfer;

/// Entry point for processing a transfer message in ICS20 token transfer
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: MsgTransfer) -> Result<HandlerOutput<PacketResult>, Error>
where
    Ctx: Ics20Context,
{
    //TODO: application logic

    let handler_output = relay_application_logic::send_transfer::send_transfer(ctx, msg)
        .map_err(|e| Kind::HandlerRaisedError.context(e))?;

    Ok(handler_output)
}
