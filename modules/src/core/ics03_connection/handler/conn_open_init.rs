//! Protocol logic specific to ICS3 messages of type `MsgConnectionOpenInit`.

use crate::{
	core::{
		ics03_connection::{
			connection::{ConnectionEnd, State},
			error::Error,
			events::Attributes,
			handler::{ConnectionIdState, ConnectionResult},
			msgs::conn_open_init::MsgConnectionOpenInit,
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
	msg: MsgConnectionOpenInit,
) -> HandlerResult<ConnectionResult, Error> {
	let mut output = HandlerOutput::builder();

	// An IBC client running on the local (host) chain should exist.
	ctx.client_state(&msg.client_id).map_err(Error::ics02_client)?;

	let versions = match msg.version {
		Some(version) =>
			if ctx.get_compatible_versions().contains(&version) {
				Ok(vec![version])
			} else {
				Err(Error::version_not_supported(version))
			},
		None => Ok(ctx.get_compatible_versions()),
	}?;

	let new_connection_end = ConnectionEnd::new(
		State::Init,
		msg.client_id.clone(),
		msg.counterparty.clone(),
		versions,
		msg.delay_period,
	);

	// Construct the identifier for the new connection.
	let id_counter = ctx.connection_counter()?;
	let conn_id = ConnectionId::new(id_counter);

	output.log(format!("success: generated new connection identifier: {}", conn_id));

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

	output.emit(IbcEvent::OpenInitConnection(event_attributes.into()));

	Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
	use test_log::test;

	use crate::{
		core::{
			ics02_client::context::ClientReader,
			ics03_connection::{
				connection::State,
				context::ConnectionReader,
				handler::{dispatch, ConnectionResult},
				msgs::{
					conn_open_init::{
						test_util::get_dummy_raw_msg_conn_open_init, MsgConnectionOpenInit,
					},
					ConnectionMsg,
				},
				version::Version,
			},
		},
		events::IbcEvent,
		mock::context::{MockClientTypes, MockContext},
		prelude::*,
		Height,
	};

	use ibc_proto::ibc::core::connection::v1::Version as RawVersion;

	#[test]
	fn conn_open_init_msg_processing() {
		struct Test {
			name: String,
			ctx: MockContext<MockClientTypes>,
			msg: ConnectionMsg<MockContext<MockClientTypes>>,
			expected_versions: Vec<Version>,
			want_pass: bool,
		}

		let msg_conn_init_default =
			MsgConnectionOpenInit::try_from(get_dummy_raw_msg_conn_open_init()).unwrap();
		let msg_conn_init_no_version =
			MsgConnectionOpenInit { version: None, ..msg_conn_init_default.clone() };
		let msg_conn_init_bad_version = MsgConnectionOpenInit {
			version: Version::try_from(RawVersion {
				identifier: "random identifier 424242".to_string(),
				features: vec![],
			})
			.unwrap()
			.into(),
			..msg_conn_init_default.clone()
		};
		let default_context = MockContext::default();
		let good_context = default_context
			.clone()
			.with_client(&msg_conn_init_default.client_id, Height::new(0, 10));

		let tests: Vec<Test> = vec![
			Test {
				name: "Processing fails because no client exists in the context".to_string(),
				ctx: default_context,
				msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_default.clone()),
				expected_versions: vec![msg_conn_init_default.version.clone().unwrap()],
				want_pass: false,
			},
			Test {
				name: "Incompatible version in MsgConnectionOpenInit msg".to_string(),
				ctx: good_context.clone(),
				msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_bad_version),
				expected_versions: vec![],
				want_pass: false,
			},
			Test {
				name: "No version in MsgConnectionOpenInit msg".to_string(),
				ctx: good_context.clone(),
				msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_no_version),
				expected_versions: good_context.get_compatible_versions(),
				want_pass: true,
			},
			Test {
				name: "Good parameters".to_string(),
				ctx: good_context,
				msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_default.clone()),
				expected_versions: vec![msg_conn_init_default.version.unwrap()],
				want_pass: true,
			},
		]
		.into_iter()
		.collect();

		for test in tests {
			let res = dispatch(&test.ctx, test.msg.clone());
			// Additionally check the events and the output objects in the result.
			match res {
				Ok(proto_output) => {
					assert!(!proto_output.events.is_empty()); // Some events must exist.

					// The object in the output is a ConnectionEnd, should have init state.
					let res: ConnectionResult = proto_output.result;
					assert_eq!(res.connection_end.state().clone(), State::Init);

					for e in proto_output.events.iter() {
						assert!(matches!(e, &IbcEvent::OpenInitConnection(_)));
						assert_eq!(e.height(), test.ctx.host_height());
					}

					assert_eq!(res.connection_end.versions(), test.expected_versions);

					// This needs to be last
					assert!(
                        test.want_pass,
                        "conn_open_init: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
				},
				Err(e) => {
					assert!(
						!test.want_pass,
						"conn_open_init: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
