use crate::applications::transfer::context::Ics20Context;
use crate::applications::transfer::error::Error as Ics20Error;
use crate::applications::transfer::events::DenomTraceEvent;
use crate::applications::transfer::packet::PacketData;
use crate::applications::transfer::{is_receiver_chain_source, TracePrefix};
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics26_routing::context::{ModuleOutputBuilder, WriteFn};
use crate::prelude::*;

pub fn process_recv_packet<Ctx: 'static + Ics20Context>(
    ctx: &Ctx,
    output: &mut ModuleOutputBuilder,
    packet: &Packet,
    data: PacketData,
) -> Result<Box<WriteFn>, Ics20Error> {
    if !ctx.is_receive_enabled() {
        return Err(Ics20Error::receive_disabled());
    }

    let receiver_account = data
        .receiver
        .clone()
        .try_into()
        .map_err(|_| Ics20Error::parse_account_failure())?;

    if is_receiver_chain_source(
        packet.source_port.clone(),
        packet.source_channel.clone(),
        &data.token.denom,
    ) {
        // sender chain is not the source, unescrow tokens
        let prefix = TracePrefix::new(packet.source_port.clone(), packet.source_channel.clone());
        let coin = {
            let mut c = data.token;
            c.denom.remove_trace_prefix(&prefix);
            c
        };

        let escrow_address =
            ctx.get_channel_escrow_address(&packet.destination_port, &packet.destination_channel)?;

        Ok(Box::new(move |ctx| {
            let ctx = ctx.downcast_mut::<Ctx>().unwrap();
            ctx.send_coins(&escrow_address, &receiver_account, &coin)
                .map_err(|e| e.to_string())
        }))
    } else {
        // sender chain is the source, mint vouchers
        let prefix = TracePrefix::new(
            packet.destination_port.clone(),
            packet.destination_channel.clone(),
        );
        let coin = {
            let mut c = data.token;
            c.denom.add_trace_prefix(prefix);
            c
        };

        let denom_trace_event = DenomTraceEvent {
            trace_hash: ctx.denom_hash_string(&coin.denom),
            denom: coin.denom.clone(),
        };
        output.emit(denom_trace_event.into());

        Ok(Box::new(move |ctx| {
            let ctx = ctx.downcast_mut::<Ctx>().unwrap();
            ctx.mint_coins(&receiver_account, &coin)
                .map_err(|e| e.to_string())
        }))
    }
}
