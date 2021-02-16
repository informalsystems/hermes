//! This module implements the processing logic for ICS20 (token transfer) messages.
// TODO
use super::context::ICS20Context;
use super::error::{Error, Kind};
//use super::msgs::transfer;
use super::msgs::transfer::MsgTransfer;
////use crate::events::IBCEvent;
use crate::handler::HandlerOutput;
use super::relay_application_logic;
//use prost_types::Any;
//use tendermint_proto::Protobuf;

// pub fn deliver<Ctx>(ctx: &mut Ctx, messages: Vec<Any>) -> Result<Vec<IBCEvent>, Error>
// where
//     Ctx: ICS20Context,
// {
//     // Create a clone, which will store each intermediary stage of applying txs.
//     let mut ctx_interim = ctx.clone();
//     let mut res: Vec<IBCEvent> = vec![];

//     for any_msg in messages {
//         // Decode the proto message into a domain message, creating an ICS26 envelope.
//         let env = match any_msg.type_url.as_str() {
//             // ICS20 messages
//             transfer::TYPE_URL => {
//                 // Pop out the message and then wrap it in the corresponding type.
//                 let domain_msg = transfer::MsgTransfer::decode_vec(&any_msg.value)
//                     .map_err(|e| Kind::MalformedMessageBytes.context(e))?;
//                 Ok(domain_msg);
//             }
//             _ => Err(Kind::UnknownMessageTypeURL(any_msg.type_url)),
//         }?;
//         let mut output = dispatch(&mut ctx_interim, env)?;
//         res.append(&mut output.events);
//     }
//     *ctx = ctx_interim;
//     Ok(res)
// }

/// Entry point for processing a transfer message in ICS20 token transfrom
pub fn dispatch<Ctx>(ctx: &Ctx, msg: MsgTransfer) -> Result<HandlerOutput<()>, Error>
// //() - > SendTransferResult ?
where
    Ctx: ICS20Context,
 {
//     // 	// sender, err := sdk.AccAddressFromBech32(msg.Sender)
//     // 	// if err != nil {
//     // 	// 	return nil, err
//     // 	// }
//     // 	if err := relay::send_transfer(
//     // 		ctx, msg.SourcePort, msg.SourceChannel, msg.Token, sender, msg.Receiver, msg.TimeoutHeight, msg.TimeoutTimestamp,
//     // 	); err != nil {
//     // 		return nil, err
//     // 	}
    let handler_output = relay_application_logic::send_transfer::send_transfer(ctx, msg)
        .map_err(|e| Kind::HandlerRaisedError.context(e))?;

//     // 	k.Logger(ctx).Info("IBC fungible token transfer", "token", msg.Token.Denom, "amount", msg.Token.Amount.String(), "sender", msg.Sender, "receiver", msg.Receiver)

//     // 	ctx.EventManager().EmitEvents(sdk.Events{
//     // 		sdk.NewEvent(
//     // 			types.EventTypeTransfer,
//     // 			sdk.NewAttribute(sdk.AttributeKeySender, msg.Sender),
//     // 			sdk.NewAttribute(types.AttributeKeyReceiver, msg.Receiver),
//     // 		),
//     // 		sdk.NewEvent(
//     // 			sdk.EventTypeMessage,
//     // 			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
//     // 		),
//     // 	})
    let output = HandlerOutput::builder()
        .with_log(handler_output.log)
        .with_events(handler_output.events)
        .with_result(());
    Ok(output)
}
