//! This module implements the processing logic for ICS20 (token transfer) transfer message.

pub mod send_transfer;

use super::error::{Error, Kind};
use super::msgs::transfer::MsgTransfer;
use super::relay_application_logic;
use crate::{ics04_channel::packet_handler::PacketResult, ics26_routing::context::ICS26Context};
use crate::handler::HandlerOutput;

/// Entry point for processing a transfer message in ICS20 token transfrom
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: MsgTransfer) -> Result<HandlerOutput<PacketResult>, Error>
where
    Ctx: ICS26Context,
{
 
   //TODO: application logic 

    let handler_output = relay_application_logic::send_transfer::send_transfer(ctx, msg)
        .map_err(|e| Kind::HandlerRaisedError.context(e))?;

    Ok(handler_output)
}
