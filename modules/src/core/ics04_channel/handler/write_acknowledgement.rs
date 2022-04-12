use crate::core::ics04_channel::channel::State;
use crate::core::ics04_channel::context::ChannelCapabilityReader;
use crate::core::ics04_channel::events::WriteAcknowledgement;
use crate::core::ics04_channel::packet::{Packet, PacketResult, Sequence};
use crate::core::ics04_channel::{context::ChannelReader, error::Error};
use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::core::ics26_routing::context::CoreModuleId;
use crate::prelude::*;
use crate::{
    events::IbcEvent,
    handler::{HandlerOutput, HandlerResult},
};

#[derive(Clone, Debug)]
pub struct WriteAckPacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub seq: Sequence,
    pub ack: Vec<u8>,
}

pub fn process<Ctx, Cap>(
    ctx: &Ctx,
    packet: Packet,
    ack: Vec<u8>,
    channel_cap: Cap,
) -> HandlerResult<PacketResult, Error>
where
    Ctx: ChannelReader + ChannelCapabilityReader<CoreModuleId, Capability = Cap>,
    Cap: Capability,
{
    let mut output = HandlerOutput::builder();

    let dest_channel_end =
        ctx.channel_end(&(packet.destination_port.clone(), packet.destination_channel))?;

    if !dest_channel_end.state_matches(&State::Open) {
        return Err(Error::invalid_channel_state(
            packet.source_channel,
            dest_channel_end.state,
        ));
    }

    ctx.authenticate_channel_capability(
        packet.source_port.clone(),
        packet.source_channel,
        &channel_cap,
    )?;

    // NOTE: IBC app modules might have written the acknowledgement synchronously on
    // the OnRecvPacket callback so we need to check if the acknowledgement is already
    // set on the store and return an error if so.
    match ctx.get_packet_acknowledgement(&(
        packet.destination_port.clone(),
        packet.destination_channel,
        packet.sequence,
    )) {
        Ok(_) => return Err(Error::acknowledgement_exists(packet.sequence)),
        Err(e)
            if e.detail() == Error::packet_acknowledgement_not_found(packet.sequence).detail() => {}
        Err(e) => return Err(e),
    }

    if ack.is_empty() {
        return Err(Error::invalid_acknowledgement());
    }

    let result = PacketResult::WriteAck(WriteAckPacketResult {
        port_id: packet.source_port.clone(),
        channel_id: packet.source_channel,
        seq: packet.sequence,
        ack: ack.clone(),
    });

    output.log("success: packet write acknowledgement");

    output.emit(IbcEvent::WriteAcknowledgement(WriteAcknowledgement {
        height: ctx.host_height(),
        packet,
        ack,
    }));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use crate::core::ics02_client::height::Height;
    use crate::core::ics03_connection::connection::ConnectionEnd;
    use crate::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::core::ics03_connection::connection::State as ConnectionState;
    use crate::core::ics03_connection::version::get_compatible_versions;
    use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
    use crate::core::ics04_channel::context::{ChannelCapabilityReader, ChannelReader};
    use crate::core::ics04_channel::handler::write_acknowledgement::process;
    use crate::core::ics04_channel::packet::test_utils::get_dummy_raw_packet;
    use crate::core::ics04_channel::Version;
    use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
    use crate::mock::context::{MockCapability, MockContext};
    use crate::prelude::*;
    use crate::timestamp::ZERO_DURATION;
    use crate::{core::ics04_channel::packet::Packet, events::IbcEvent};

    #[test]
    fn write_ack_packet_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            packet: Packet,
            ack: Vec<u8>,
            want_pass: bool,
        }

        let context = MockContext::default();

        let client_height = Height::new(0, 1);

        let mut packet: Packet = get_dummy_raw_packet(1, 6).try_into().unwrap();
        packet.sequence = 1.into();
        packet.data = vec![0];

        let ack = vec![0];
        let ack_null = Vec::new();

        let dest_channel_end = ChannelEnd::new(
            State::Open,
            Order::default(),
            Counterparty::new(packet.source_port.clone(), Some(packet.source_channel)),
            vec![ConnectionId::default()],
            Version::ics20(),
        );

        let connection_end = ConnectionEnd::new(
            ConnectionState::Open,
            ClientId::default(),
            ConnectionCounterparty::new(
                ClientId::default(),
                Some(ConnectionId::default()),
                Default::default(),
            ),
            get_compatible_versions(),
            ZERO_DURATION,
        );

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no channel exists in the context".to_string(),
                ctx: context.clone(),
                packet: packet.clone(),
                ack: ack.clone(),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the port does not have a capability associated"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_channel(
                        PortId::default(),
                        ChannelId::default(),
                        dest_channel_end.clone(),
                    )
                    .without_ocap(),
                packet: packet.clone(),
                ack: ack.clone(),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(
                        packet.destination_port.clone(),
                        packet.destination_channel,
                        dest_channel_end.clone(),
                    ),
                packet: packet.clone(),
                ack,
                want_pass: true,
            },
            Test {
                name: "Zero ack".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), Height::default())
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_channel(PortId::default(), ChannelId::default(), dest_channel_end),
                packet,
                ack: ack_null,
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let channel_cap = test
                .ctx
                .lookup_module_by_channel(ChannelId::default(), PortId::default())
                .map(|(_, cap)| cap)
                .unwrap_or_else(|_| MockCapability::new(0));

            let res = process(&test.ctx, test.packet.clone(), test.ack, channel_cap);
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert!(
                        test.want_pass,
                        "write_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone()
                    );

                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::WriteAcknowledgement(_)));
                        assert_eq!(e.height(), test.ctx.host_height());
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "write_ack: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}
