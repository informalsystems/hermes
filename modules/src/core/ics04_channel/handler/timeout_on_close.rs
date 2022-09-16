use crate::{
	core::{
		ics04_channel::{
			channel::{ChannelEnd, Counterparty, Order, State},
			error::Error,
			events::TimeoutOnClosePacket,
			handler::{
				timeout::TimeoutPacketResult,
				verify::{
					verify_channel_proofs, verify_next_sequence_recv, verify_packet_receipt_absence,
				},
			},
			msgs::timeout_on_close::MsgTimeoutOnClose,
			packet::PacketResult,
		},
		ics26_routing::context::ReaderContext,
	},
	events::IbcEvent,
	handler::{HandlerOutput, HandlerResult},
	prelude::*,
};

pub fn process<Ctx: ReaderContext>(
	ctx: &Ctx,
	msg: &MsgTimeoutOnClose,
) -> HandlerResult<PacketResult, Error> {
	let mut output = HandlerOutput::builder();

	let packet = &msg.packet;

	let source_channel_end =
		ctx.channel_end(&(packet.source_port.clone(), packet.source_channel))?;

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

	//verify the packet was sent, check the store
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

	let expected_counterparty =
		Counterparty::new(packet.source_port.clone(), Some(packet.source_channel));

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

	verify_channel_proofs::<Ctx>(
		ctx,
		msg.proofs.height(),
		&source_channel_end,
		&connection_end,
		&expected_channel_end,
		msg.proofs
			.other_proof()
			.as_ref()
			.ok_or_else(|| Error::missing_channel_proof())?,
	)?;

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

	output.emit(IbcEvent::TimeoutOnClosePacket(TimeoutOnClosePacket {
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
				handler::timeout_on_close::process,
				msgs::timeout_on_close::{
					test_util::get_dummy_raw_msg_timeout_on_close, MsgTimeoutOnClose,
				},
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
	fn timeout_on_close_packet_processing() {
		struct Test {
			name: String,
			ctx: MockContext<MockClientTypes>,
			msg: MsgTimeoutOnClose,
			want_pass: bool,
		}

		let context = MockContext::default();

		let height = Height::default().revision_height + 2;
		let timeout_timestamp = 5;

		let client_height = Height::new(0, Height::default().revision_height + 2);

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
			Counterparty::new(packet.destination_port.clone(), Some(packet.destination_channel)),
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
						packet.source_port.clone(),
						packet.source_channel,
						source_channel_end,
					)
					.with_packet_commitment(
						msg.packet.source_port.clone(),
						msg.packet.source_channel,
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
