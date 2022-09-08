use crate::core::ics04_channel::channel::State;
use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, Order};
use crate::core::ics04_channel::events::TimeoutOnClosePacket;
use crate::core::ics04_channel::handler::verify::verify_channel_proofs;
use crate::core::ics04_channel::handler::verify::{
    verify_next_sequence_recv, verify_packet_receipt_absence,
};
use crate::core::ics04_channel::msgs::timeout_on_close::MsgTimeoutOnClose;
use crate::core::ics04_channel::packet::PacketResult;
use crate::core::ics04_channel::{
    context::ChannelReader, error::Error, handler::timeout::TimeoutPacketResult,
};
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;
use crate::proofs::{ProofError, Proofs};

pub fn process<Ctx: ChannelReader>(
    ctx: &Ctx,
    msg: &MsgTimeoutOnClose,
) -> HandlerResult<PacketResult, Error> {
    let mut output = HandlerOutput::builder();

    let packet = &msg.packet;

    let source_channel_end = ctx.channel_end(&packet.source_port, &packet.source_channel)?;

    let counterparty = Counterparty::new(
        packet.destination_port.clone(),
        Some(packet.destination_channel.clone()),
    );

    if !source_channel_end.counterparty_matches(&counterparty) {
        return Err(Error::invalid_packet_counterparty(
            packet.destination_port.clone(),
            packet.destination_channel.clone(),
        ));
    }

    let connection_end = ctx.connection_end(&source_channel_end.connection_hops()[0])?;

    //verify the packet was sent, check the store
    let packet_commitment =
        ctx.get_packet_commitment(&packet.source_port, &packet.source_channel, packet.sequence)?;

    let expected_commitment = ctx.packet_commitment(
        packet.data.clone(),
        packet.timeout_height,
        packet.timeout_timestamp,
    );
    if packet_commitment != expected_commitment {
        return Err(Error::incorrect_packet_commitment(packet.sequence));
    }

    let expected_counterparty = Counterparty::new(
        packet.source_port.clone(),
        Some(packet.source_channel.clone()),
    );

    let counterparty = connection_end.counterparty();
    let ccid = counterparty.connection_id().ok_or_else(|| {
        Error::undefined_connection_counterparty(source_channel_end.connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::Closed,
        *source_channel_end.ordering(),
        expected_counterparty,
        expected_connection_hops,
        source_channel_end.version().clone(),
    );

    // The message's proofs have the channel proof as `other_proof`
    let proof_close = match msg.proofs.other_proof() {
        Some(p) => p.clone(),
        None => return Err(Error::invalid_proof(ProofError::empty_proof())),
    };
    let proofs = Proofs::new(proof_close, None, None, None, msg.proofs.height())
        .map_err(Error::invalid_proof)?;
    verify_channel_proofs(
        ctx,
        msg.proofs.height(),
        &source_channel_end,
        &connection_end,
        &expected_channel_end,
        &proofs,
    )?;

    let result = if source_channel_end.order_matches(&Order::Ordered) {
        if packet.sequence < msg.next_sequence_recv {
            return Err(Error::invalid_packet_sequence(
                packet.sequence,
                msg.next_sequence_recv,
            ));
        }
        verify_next_sequence_recv(
            ctx,
            msg.proofs.height(),
            &connection_end,
            packet.clone(),
            msg.next_sequence_recv,
            &msg.proofs,
        )?;

        PacketResult::Timeout(TimeoutPacketResult {
            port_id: packet.source_port.clone(),
            channel_id: packet.source_channel.clone(),
            seq: packet.sequence,
            channel: Some(source_channel_end),
        })
    } else {
        verify_packet_receipt_absence(
            ctx,
            msg.proofs.height(),
            &connection_end,
            packet.clone(),
            &msg.proofs,
        )?;

        PacketResult::Timeout(TimeoutPacketResult {
            port_id: packet.source_port.clone(),
            channel_id: packet.source_channel.clone(),
            seq: packet.sequence,
            channel: None,
        })
    };

    output.log("success: packet timeout ");

    output.emit(IbcEvent::TimeoutOnClosePacket(TimeoutOnClosePacket {
        packet: packet.clone(),
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
    use crate::core::ics04_channel::context::ChannelReader;
    use crate::core::ics04_channel::handler::timeout_on_close::process;
    use crate::core::ics04_channel::msgs::timeout_on_close::test_util::get_dummy_raw_msg_timeout_on_close;
    use crate::core::ics04_channel::msgs::timeout_on_close::MsgTimeoutOnClose;
    use crate::core::ics04_channel::Version;
    use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
    use crate::events::IbcEvent;
    use crate::mock::context::MockContext;
    use crate::prelude::*;
    use crate::timestamp::ZERO_DURATION;

    #[test]
    fn timeout_on_close_packet_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: MsgTimeoutOnClose,
            want_pass: bool,
        }

        let context = MockContext::default();

        let height = 2;
        let timeout_timestamp = 5;

        let client_height = Height::new(0, 2).unwrap();

        let msg = MsgTimeoutOnClose::try_from(get_dummy_raw_msg_timeout_on_close(
            height,
            timeout_timestamp,
        ))
        .unwrap();
        let packet = msg.packet.clone();

        let data = context.packet_commitment(
            msg.packet.data.clone(),
            msg.packet.timeout_height,
            msg.packet.timeout_timestamp,
        );

        let source_channel_end = ChannelEnd::new(
            State::Open,
            Order::Ordered,
            Counterparty::new(
                packet.destination_port.clone(),
                Some(packet.destination_channel),
            ),
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
                msg: msg.clone(),
                want_pass: false,
            },
            Test {
                name: "Processing fails no packet commitment is found".to_string(),
                ctx: context
                    .clone()
                    .with_channel(
                        PortId::default(),
                        ChannelId::default(),
                        source_channel_end.clone(),
                    )
                    .with_connection(ConnectionId::default(), connection_end.clone()),
                msg: msg.clone(),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_channel(
                        packet.source_port,
                        packet.source_channel,
                        source_channel_end,
                    )
                    .with_packet_commitment(
                        msg.packet.source_port.clone(),
                        msg.packet.source_channel.clone(),
                        msg.packet.sequence,
                        data,
                    ),
                msg,
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = process(&test.ctx, &test.msg);
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert!(
                        test.want_pass,
                        "TO_on_close_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );

                    assert!(!proto_output.events.is_empty()); // Some events must exist.
                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::TimeoutOnClosePacket(_)));
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "timeout_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}
