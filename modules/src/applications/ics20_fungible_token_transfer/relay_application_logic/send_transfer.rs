use crate::applications::ics20_fungible_token_transfer::context::Ics20Context;
use crate::applications::ics20_fungible_token_transfer::error::Error;
use crate::applications::ics20_fungible_token_transfer::events::TransferEvent;
use crate::applications::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
use crate::applications::ics20_fungible_token_transfer::packet::PacketData;
use crate::applications::ics20_fungible_token_transfer::{Coin, IbcCoin, Source, TracePrefix};
use crate::core::ics04_channel::handler::send_packet::send_packet;
use crate::core::ics04_channel::packet::Packet;
use crate::events::ModuleEvent;
use crate::handler::{HandlerOutput, HandlerOutputBuilder};
use crate::prelude::*;

pub fn send_transfer<Ctx>(
    ctx: &mut Ctx,
    output: &mut HandlerOutputBuilder<()>,
    msg: MsgTransfer,
) -> Result<(), Error>
where
    Ctx: Ics20Context,
{
    if !ctx.is_send_enabled() {
        return Err(Error::send_disabled());
    }

    let source_channel_end = ctx
        .channel_end(&(msg.source_port.clone(), msg.source_channel))
        .map_err(Error::ics04_channel)?;

    let destination_port = source_channel_end.counterparty().port_id().clone();
    let destination_channel = *source_channel_end
        .counterparty()
        .channel_id()
        .ok_or_else(|| {
            Error::destination_channel_not_found(msg.source_port.clone(), msg.source_channel)
        })?;

    // get the next sequence
    let sequence = ctx
        .get_next_sequence_send(&(msg.source_port.clone(), msg.source_channel))
        .map_err(Error::ics04_channel)?;

    let denom = match msg.token.clone() {
        IbcCoin::Hashed(coin) => ctx
            .get_denom_trace(&coin.denom)
            .ok_or_else(Error::trace_not_found)?,
        IbcCoin::Base(coin) => coin.denom.into(),
    };

    let sender = msg
        .sender
        .clone()
        .try_into()
        .map_err(|_| Error::parse_account_failure())?;

    let prefix = TracePrefix::new(msg.source_port.clone(), msg.source_channel);
    match denom.source_chain(&prefix) {
        Source::Sender => {
            let escrow_address =
                ctx.get_channel_escrow_address(&msg.source_port, msg.source_channel)?;
            ctx.send_coins(&sender, &escrow_address, &msg.token)?;
        }
        Source::Receiver => {
            ctx.send_coins_from_account_to_module(
                &sender,
                &ctx.get_transfer_account(),
                &msg.token,
            )?;
            ctx.burn_coins(&ctx.get_transfer_account(), &msg.token)
                .expect("cannot burn coins after a successful send to a module account");
        }
    }

    let data = {
        let data = PacketData {
            token: Coin {
                denom,
                amount: msg.token.amount(),
            },
            sender: msg.sender.clone(),
            receiver: msg.receiver.clone(),
        };
        serde_json::to_vec(&data).expect("PacketData's infallible Serialize impl failed")
    };

    let packet = Packet {
        sequence,
        source_port: msg.source_port,
        source_channel: msg.source_channel,
        destination_port,
        destination_channel,
        data,
        timeout_height: msg.timeout_height,
        timeout_timestamp: msg.timeout_timestamp,
    };

    let HandlerOutput {
        result,
        log,
        events,
    } = send_packet(ctx, packet).map_err(Error::ics04_channel)?;

    ctx.store_packet_result(result)
        .map_err(Error::ics04_channel)?;

    output.merge_output(
        HandlerOutput::builder()
            .with_log(log)
            .with_events(events)
            .with_result(()),
    );

    output.log(format!(
        "IBC fungible token transfer: {} --({})--> {}",
        msg.sender, msg.token, msg.receiver
    ));

    let transfer_event = TransferEvent {
        sender: msg.sender,
        receiver: msg.receiver,
    };
    output.emit(ModuleEvent::from(transfer_event).into());

    Ok(())
}
