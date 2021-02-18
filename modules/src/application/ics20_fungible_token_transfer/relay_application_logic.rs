//! This module implements the processing logic for ICS20 (token transfer) transfer message.

pub mod send_transfer;

// TODO
use super::context::ICS20Context;
use super::error::{Error, Kind};
use super::msgs::transfer;
use super::msgs::transfer::MsgTransfer;
use super::relay_application_logic;
use crate::events::IBCEvent;
use crate::handler::HandlerOutput;
use prost_types::Any;
use tendermint_proto::Protobuf;

pub fn deliver<Ctx>(ctx: &mut Ctx, messages: Vec<Any>) -> Result<Vec<IBCEvent>, Error>
where
    Ctx: ICS20Context,
{
    // Create a clone, which will store each intermediary stage of applying txs.
    let mut ctx_interim = ctx.clone();
    let mut res: Vec<IBCEvent> = vec![];

    for any_msg in messages {
        // Decode the proto message into a domain message, creating an ICS26 envelope.
        let env = match any_msg.type_url.as_str() {
            // ICS20 messages
            transfer::TYPE_URL => {
                // Pop out the message and then wrap it in the corresponding type.
                let domain_msg = transfer::MsgTransfer::decode_vec(&any_msg.value)
                    .map_err(|e| Kind::MalformedMessageBytes.context(e))?;
                Ok(domain_msg)
            }
            _ => Err(Kind::UnknownMessageTypeURL(any_msg.type_url)),
        }?;
        let mut output = dispatch(&mut ctx_interim, env)?;
        res.append(&mut output.events);
    }
    *ctx = ctx_interim;
    Ok(res)
}

/// Entry point for processing a transfer message in ICS20 token transfrom
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: MsgTransfer) -> Result<HandlerOutput<()>, Error>
where
    Ctx: ICS20Context,
{
 
   //TODO: application logic 

    let handler_output = relay_application_logic::send_transfer::send_transfer(ctx, msg)
        .map_err(|e| Kind::HandlerRaisedError.context(e))?;

    ctx.store_packet_result(handler_output.result).map_err(|e| Kind::KeeperRaisedError.context(e))?;

    let output = HandlerOutput::builder()
        .with_log(handler_output.log)
        .with_events(handler_output.events)
        .with_result(());
    Ok(output)
}
