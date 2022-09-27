use crate::applications::transfer::context::Ics20Context;
use crate::applications::transfer::error::Error;
use crate::applications::transfer::events::TransferEvent;
use crate::applications::transfer::msgs::transfer::MsgTransfer;
use crate::applications::transfer::packet::PacketData;
use crate::applications::transfer::{is_sender_chain_source, Coin, PrefixedCoin};
use crate::core::ics04_channel::handler::send_packet::send_packet;
use crate::core::ics04_channel::packet::Packet;
use crate::events::ModuleEvent;
use crate::handler::{HandlerOutput, HandlerOutputBuilder};
use crate::prelude::*;

/// This function handles the transfer sending logic.
/// If this method returns an error, the runtime is expected to rollback all state modifications to
/// the `Ctx` caused by all messages from the transaction that this `msg` is a part of.
pub fn send_transfer<Ctx, C>(
    ctx: &mut Ctx,
    output: &mut HandlerOutputBuilder<()>,
    msg: MsgTransfer<C>,
) -> Result<(), Error>
where
    Ctx: Ics20Context,
    C: TryInto<PrefixedCoin>,
{
    if !ctx.is_send_enabled() {
        return Err(Error::send_disabled());
    }

    let source_channel_end = ctx
        .channel_end(&msg.source_port, &msg.source_channel)
        .map_err(Error::ics04_channel)?;

    let destination_port = source_channel_end.counterparty().port_id().clone();
    let destination_channel = source_channel_end
        .counterparty()
        .channel_id()
        .ok_or_else(|| {
            Error::destination_channel_not_found(
                msg.source_port.clone(),
                msg.source_channel.clone(),
            )
        })?
        .clone();

    // get the next sequence
    let sequence = ctx
        .get_next_sequence_send(&msg.source_port, &msg.source_channel)
        .map_err(Error::ics04_channel)?;

    let token = msg.token.try_into().map_err(|_| Error::invalid_token())?;
    let denom = token.denom.clone();
    let coin = Coin {
        denom: denom.clone(),
        amount: token.amount,
    };

    let sender = msg
        .sender
        .clone()
        .try_into()
        .map_err(|_| Error::parse_account_failure())?;

    if is_sender_chain_source(msg.source_port.clone(), msg.source_channel.clone(), &denom) {
        let escrow_address =
            ctx.get_channel_escrow_address(&msg.source_port, &msg.source_channel)?;
        ctx.send_coins(&sender, &escrow_address, &coin)?;
    } else {
        ctx.burn_coins(&sender, &coin)?;
    }

    let data = {
        let data = PacketData {
            token: coin,
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
        msg.sender, token, msg.receiver
    ));

    let transfer_event = TransferEvent {
        sender: msg.sender,
        receiver: msg.receiver,
    };
    output.emit(ModuleEvent::from(transfer_event).into());

    Ok(())
}
