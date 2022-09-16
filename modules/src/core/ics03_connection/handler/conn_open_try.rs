//! Protocol logic specific to processing ICS3 messages of type `MsgConnectionOpenTry`.

use crate::{
	core::{
		ics03_connection::{
			connection::{ConnectionEnd, Counterparty, State},
			error::Error,
			events::Attributes,
			handler::{
				verify::{
					check_client_consensus_height, verify_client_proof, verify_connection_proof,
					verify_consensus_proof,
				},
				ConnectionIdState, ConnectionResult,
			},
			msgs::conn_open_try::MsgConnectionOpenTry,
		},
		ics24_host::identifier::ConnectionId,
		ics26_routing::context::ReaderContext,
	},
	events::IbcEvent,
	handler::{HandlerOutput, HandlerResult},
	prelude::*,
};

pub(crate) fn process<Ctx: ReaderContext>(
	ctx: &Ctx,
	msg: MsgConnectionOpenTry<Ctx>,
) -> HandlerResult<ConnectionResult, Error> {
	let mut output = HandlerOutput::builder();

	// Check that consensus height if provided (for client proof) in message is not too advanced nor
	// too old.
	if msg.proofs.consensus_proof().is_some() {
		check_client_consensus_height(ctx, msg.consensus_height())?;
	}

	// Unwrap the old connection end (if any) and its identifier.
	let (mut new_connection_end, conn_id) = {
		// Build a new connection end as well as an identifier.
		let conn_end = ConnectionEnd::new(
			State::Init,
			msg.client_id.clone(),
			msg.counterparty.clone(),
			msg.counterparty_versions.clone(),
			msg.delay_period,
		);
		let id_counter = ctx.connection_counter()?;
		let conn_id = ConnectionId::new(id_counter);

		output.log(format!("success: new connection end and identifier {} generated", conn_id));
		(conn_end, conn_id)
	};

	// Proof verification in two steps:
	// 1. Setup: build the ConnectionEnd as we expect to find it on the other party.
	let expected_conn = ConnectionEnd::new(
		State::Init,
		msg.counterparty.client_id().clone(),
		Counterparty::new(msg.client_id.clone(), None, ctx.commitment_prefix()),
		msg.counterparty_versions.clone(),
		msg.delay_period,
	);

	let client_state = msg.client_state.ok_or_else(|| {
		Error::implementation_specific("client state is required in connOpenTry".into())
	})?;

	let client_proof = msg.proofs.client_proof().as_ref().ok_or_else(|| {
		Error::implementation_specific("client proof is required in connOpenTry".into())
	})?;

	let consensus_proof = msg.proofs.consensus_proof().ok_or_else(|| {
		Error::implementation_specific("consensus proof is required in connOpenTry".into())
	})?;

	ctx.validate_self_client(&client_state).map_err(Error::ics02_client)?;

	verify_connection_proof::<_>(
		ctx,
		msg.proofs.height(),
		&new_connection_end,
		&expected_conn,
		msg.proofs.height(),
		msg.proofs.object_proof(),
	)?;

	verify_client_proof::<_>(
		ctx,
		msg.proofs.height(),
		&new_connection_end,
		client_state,
		msg.proofs.height(),
		client_proof,
	)?;

	verify_consensus_proof::<_>(ctx, msg.proofs.height(), &new_connection_end, &consensus_proof)?;

	// Transition the connection end to the new state & pick a version.
	new_connection_end.set_state(State::TryOpen);

	// Pick the version.
	new_connection_end.set_version(
		ctx.pick_version(ctx.get_compatible_versions(), msg.counterparty_versions.clone())?,
	);

	assert_eq!(new_connection_end.versions().len(), 1);

	output.log("success: connection verification passed");

	let event_attributes = Attributes {
		connection_id: Some(conn_id.clone()),
		height: ctx.host_height(),
		client_id: new_connection_end.client_id().clone(),
		counterparty_connection_id: new_connection_end.counterparty().connection_id.clone(),
		counterparty_client_id: new_connection_end.counterparty().client_id().clone(),
	};

	let result = ConnectionResult {
		connection_id: conn_id,
		connection_id_state: ConnectionIdState::Generated,
		connection_end: new_connection_end,
	};

	output.emit(IbcEvent::OpenTryConnection(event_attributes.into()));

	Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	use test_log::test;

	use crate::{
		core::{
			ics02_client::context::ClientReader,
			ics03_connection::{
				connection::State,
				handler::{dispatch, ConnectionResult},
				msgs::{
					conn_open_try::{
						test_util::get_dummy_raw_msg_conn_open_try, MsgConnectionOpenTry,
					},
					ConnectionMsg,
				},
			},
			ics24_host::identifier::ChainId,
		},
		events::IbcEvent,
		mock::{
			context::{MockClientTypes, MockContext},
			host::MockHostType,
		},
		Height,
	};

	#[test]
	fn conn_open_try_msg_processing() {
		struct Test {
			name: String,
			ctx: MockContext<MockClientTypes>,
			msg: ConnectionMsg<MockContext<MockClientTypes>>,
			want_pass: bool,
		}

		let host_chain_height = Height::new(0, 35);
		let max_history_size = 5;
		let context = MockContext::new(
			ChainId::new("mockgaia".to_string(), 0),
			MockHostType::Mock,
			max_history_size,
			host_chain_height,
		);
		let client_consensus_state_height = 10;

		let msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
			client_consensus_state_height,
			host_chain_height.revision_height,
		))
		.unwrap();

		// The proof targets a height that does not exist (i.e., too advanced) on destination chain.
		let msg_height_advanced = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
			client_consensus_state_height,
			host_chain_height.increment().revision_height,
		))
		.unwrap();
		let pruned_height =
			host_chain_height.sub(max_history_size as u64 + 1).unwrap().revision_height;
		// The consensus proof targets a missing height (pruned) on destination chain.
		let msg_height_old = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
			client_consensus_state_height,
			pruned_height,
		))
		.unwrap();

		// The proofs in this message are created at a height which the client on destination chain
		// does not have.
		let msg_proof_height_missing =
			MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
				client_consensus_state_height - 1,
				host_chain_height.revision_height,
			))
			.unwrap();

		let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because the height is too advanced".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_height_advanced)),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the height is too old".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_height_old)),
                want_pass: false,
            },
            Test {
                name: "Processing fails because no client exists".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_conn_try.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the client misses the consensus state targeted by the proof".to_string(),
                ctx: context.clone().with_client(&msg_proof_height_missing.client_id, Height::new(0, client_consensus_state_height)),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_proof_height_missing)),
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

		for test in tests {
			let res = dispatch(&test.ctx, test.msg.clone());
			// Additionally check the events and the output objects in the result.
			match res {
				Ok(proto_output) => {
					assert!(
                        test.want_pass,
                        "conn_open_try: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );

					assert!(!proto_output.events.is_empty()); // Some events must exist.

					// The object in the output is a ConnectionEnd, should have TryOpen state.
					let res: ConnectionResult = proto_output.result;
					assert_eq!(res.connection_end.state().clone(), State::TryOpen);

					for e in proto_output.events.iter() {
						assert!(matches!(e, &IbcEvent::OpenTryConnection(_)));
						assert_eq!(e.height(), test.ctx.host_height());
					}
				},
				Err(e) => {
					assert!(
						!test.want_pass,
						"conn_open_try: failed for test: {}, \nparams {:?} {:?} error: {:?}",
						test.name,
						test.msg,
						test.ctx.clone(),
						e,
					);
				},
			}
		}
	}
}
