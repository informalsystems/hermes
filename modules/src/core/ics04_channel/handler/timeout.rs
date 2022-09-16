use crate::{
	core::{
		ics02_client::client_consensus::ConsensusState,
		ics04_channel::{
			channel::{ChannelEnd, Counterparty, Order, State},
			error::Error,
			events::TimeoutPacket,
			handler::verify::{verify_next_sequence_recv, verify_packet_receipt_absence},
			msgs::timeout::MsgTimeout,
			packet::{PacketResult, Sequence},
		},
		ics24_host::identifier::{ChannelId, PortId},
		ics26_routing::context::ReaderContext,
	},
	events::IbcEvent,
	handler::{HandlerOutput, HandlerResult},
	prelude::*,
};
use core::fmt::Debug;

#[derive(Clone, Debug)]
pub struct TimeoutPacketResult {
	pub port_id: PortId,
	pub channel_id: ChannelId,
	pub seq: Sequence,
	pub channel: Option<ChannelEnd>,
}

pub fn process<Ctx>(ctx: &Ctx, msg: &MsgTimeout) -> HandlerResult<PacketResult, Error>
where
	Ctx: ReaderContext,
{
	let mut output = HandlerOutput::builder();

	let packet = &msg.packet;

	let mut source_channel_end =
		ctx.channel_end(&(packet.source_port.clone(), packet.source_channel))?;

	if !source_channel_end.state_matches(&State::Open) {
		return Err(Error::channel_closed(packet.source_channel))
	}

	let counterparty =
		Counterparty::new(packet.destination_port.clone(), Some(packet.destination_channel));

	if !source_channel_end.counterparty_matches(&counterparty) {
		return Err(Error::invalid_packet_counterparty(
			packet.destination_port.clone(),
			packet.destination_channel,
		))
	}

	let connection_end = ctx
		.connection_end(&source_channel_end.connection_hops()[0])
		.map_err(Error::ics03_connection)?;

	let client_id = connection_end.client_id().clone();

	// check that timeout height or timeout timestamp has passed on the other end
	let proof_height = msg.proofs.height();

	let consensus_state = ctx
		.consensus_state(&client_id, proof_height)
		.map_err(|_| Error::error_invalid_consensus_state())?;

	let proof_timestamp = consensus_state.timestamp();

	if !packet.timed_out(&proof_timestamp, proof_height) {
		return Err(Error::packet_timeout_not_reached(
			packet.timeout_height,
			proof_height,
			packet.timeout_timestamp,
			proof_timestamp,
		))
	}

	//verify packet commitment
	let packet_commitment = ctx.get_packet_commitment(&(
		packet.source_port.clone(),
		packet.source_channel,
		packet.sequence,
	))?;

	let expected_commitment =
		ctx.packet_commitment(packet.data.clone(), packet.timeout_height, packet.timeout_timestamp);
	if packet_commitment != expected_commitment {
		return Err(Error::incorrect_packet_commitment(packet.sequence))
	}

	let result = if source_channel_end.order_matches(&Order::Ordered) {
		if packet.sequence < msg.next_sequence_recv {
			return Err(Error::invalid_packet_sequence(packet.sequence, msg.next_sequence_recv))
		}
		verify_next_sequence_recv::<Ctx>(
			ctx,
			msg.proofs.height(),
			&connection_end,
			packet.clone(),
			msg.next_sequence_recv,
			&msg.proofs,
		)?;

		source_channel_end.state = State::Closed;
		PacketResult::Timeout(TimeoutPacketResult {
			port_id: packet.source_port.clone(),
			channel_id: packet.source_channel,
			seq: packet.sequence,
			channel: Some(source_channel_end),
		})
	} else {
		verify_packet_receipt_absence::<Ctx>(
			ctx,
			msg.proofs.height(),
			&connection_end,
			packet.clone(),
			&msg.proofs,
		)?;

		PacketResult::Timeout(TimeoutPacketResult {
			port_id: packet.source_port.clone(),
			channel_id: packet.source_channel,
			seq: packet.sequence,
			channel: None,
		})
	};

	output.log("success: packet timeout ");

	output.emit(IbcEvent::TimeoutPacket(TimeoutPacket {
		height: ctx.host_height(),
		packet: packet.clone(),
	}));

	Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
	use test_log::test;

	use crate::{
		core::{
			ics02_client::{context::ClientReader, height::Height},
			ics03_connection::{
				connection::{
					ConnectionEnd, Counterparty as ConnectionCounterparty, State as ConnectionState,
				},
				version::get_compatible_versions,
			},
			ics04_channel::{
				channel::{ChannelEnd, Counterparty, Order, State},
				context::ChannelReader,
				handler::timeout::process,
				msgs::timeout::{test_util::get_dummy_raw_msg_timeout, MsgTimeout},
				Version,
			},
			ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
		},
		events::IbcEvent,
		mock::context::{MockClientTypes, MockContext},
		prelude::*,
		timestamp::ZERO_DURATION,
	};

	#[test]
	fn timeout_packet_processing() {
		struct Test {
			name: String,
			ctx: MockContext<MockClientTypes>,
			msg: MsgTimeout,
			want_pass: bool,
		}

		let context = MockContext::default();

		let height = Height::default().revision_height + 2;
		let timeout_timestamp = 5;

		let client_height = Height::new(0, Height::default().revision_height + 2);

		let msg =
			MsgTimeout::try_from(get_dummy_raw_msg_timeout(height, timeout_timestamp)).unwrap();
		let packet = msg.packet.clone();

		let mut msg_ok = msg.clone();
		msg_ok.packet.timeout_timestamp = Default::default();

		let data = context.packet_commitment(
			msg_ok.packet.data.clone(),
			msg_ok.packet.timeout_height,
			msg_ok.packet.timeout_timestamp,
		);

		let source_channel_end = ChannelEnd::new(
			State::Open,
			Order::default(),
			Counterparty::new(packet.destination_port.clone(), Some(packet.destination_channel)),
			vec![ConnectionId::default()],
			Version::ics20(),
		);

		let mut source_ordered_channel_end = source_channel_end.clone();
		source_ordered_channel_end.ordering = Order::Ordered;

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
                name: "Processing fails because the client does not have a consensus state for the required height"
                    .to_string(),
                ctx: context.clone().with_channel(
                    PortId::default(),
                    ChannelId::default(),
                    source_channel_end.clone(),
                )
                .with_connection(ConnectionId::default(), connection_end.clone()),
                msg: msg.clone(),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the proof's timeout has not been reached "
                    .to_string(),
                ctx: context.clone().with_channel(
                    PortId::default(),
                    ChannelId::default(),
                    source_channel_end.clone(),
                )
                .with_client(&ClientId::default(), client_height)
                .with_connection(ConnectionId::default(), connection_end.clone()),
                msg,
                want_pass: false,
            },
            Test {
                name: "Good parameters Unordered channel".to_string(),
                ctx: context.clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(
                        packet.source_port.clone(),
                        packet.source_channel,
                        source_channel_end,
                    )
                    .with_packet_commitment(
                        msg_ok.packet.source_port.clone(),
                        msg_ok.packet.source_channel,
                        msg_ok.packet.sequence,
                        data.clone(),
                    ),
                msg: msg_ok.clone(),
                want_pass: true,
            },
            Test {
                name: "Good parameters Ordered Channel".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_channel(
                        packet.source_port.clone(),
                        packet.source_channel,
                        source_ordered_channel_end,
                    )
                    .with_packet_commitment(
                        msg_ok.packet.source_port.clone(),
                        msg_ok.packet.source_channel,
                        msg_ok.packet.sequence,
                        data,
                    )
                    .with_ack_sequence(
                         packet.destination_port,
                         packet.destination_channel,
                         1.into(),
                     ),
                msg: msg_ok,
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
                        "TO_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );

					assert!(!proto_output.events.is_empty()); // Some events must exist.

					for e in proto_output.events.iter() {
						assert!(matches!(e, &IbcEvent::TimeoutPacket(_)));
						assert_eq!(e.height(), test.ctx.host_height());
					}
				},
				Err(e) => {
					assert!(
						!test.want_pass,
						"timeout_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
						test.name,
						test.msg.clone(),
						test.ctx.clone(),
						e,
					);
				},
			}
		}
	}
}
