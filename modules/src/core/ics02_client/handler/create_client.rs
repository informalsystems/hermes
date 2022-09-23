//! Protocol logic specific to processing ICS2 messages of type `MsgCreateAnyClient`.

use crate::{core::ics26_routing::context::ReaderContext, prelude::*};
use core::fmt::Debug;

use crate::core::ics02_client::client_state::{ClientState, ClientType};

use crate::core::ics02_client::context::ClientTypes;
use crate::{
	core::{
		ics02_client::{
			error::Error, events::Attributes, handler::ClientResult, height::Height,
			msgs::create_client::MsgCreateAnyClient,
		},
		ics24_host::identifier::ClientId,
	},
	events::IbcEvent,
	handler::{HandlerOutput, HandlerResult},
	timestamp::Timestamp,
};

/// The result following the successful processing of a `MsgCreateAnyClient` message. Preferably
/// this data type should be used with a qualified name `create_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result<C: ClientTypes> {
	pub client_id: ClientId,
	pub client_type: ClientType,
	pub client_state: C::AnyClientState,
	pub consensus_state: C::AnyConsensusState,
	pub processed_time: Timestamp,
	pub processed_height: Height,
}

pub fn process<Ctx>(
	ctx: &Ctx,
	msg: MsgCreateAnyClient<Ctx>,
) -> HandlerResult<ClientResult<Ctx>, Error>
where
	Ctx: ReaderContext + Eq + Debug + Clone,
{
	let mut output = HandlerOutput::builder();

	// Construct this client's identifier
	let id_counter = ctx.client_counter()?;
	let client_type = msg.client_state.client_type();
	let client_id = ClientId::new(&client_type, id_counter)
		.map_err(|e| Error::client_identifier_constructor(client_type.to_owned(), id_counter, e))?;

	output.log(format!("success: generated new client identifier: {}", client_id));

	let result = ClientResult::Create(Result {
		client_id: client_id.clone(),
		client_type: msg.client_state.client_type(),
		client_state: msg.client_state.clone(),
		consensus_state: msg.consensus_state,
		processed_time: ctx.host_timestamp(),
		processed_height: ctx.host_height(),
	});

	let event_attributes = Attributes {
		client_id,
		height: ctx.host_height(),
		client_type: msg.client_state.client_type().to_owned(),
		consensus_height: msg.client_state.latest_height(),
	};
	output.emit(IbcEvent::CreateClient(event_attributes.into()));

	Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
	use crate::core::ics02_client::client_state::ClientState;

	use crate::{
		core::{
			ics02_client::{
				context::ClientReader,
				handler::{dispatch, ClientResult},
				msgs::{create_client::MsgCreateAnyClient, ClientMsg},
			},
			ics24_host::identifier::ClientId,
		},
		events::IbcEvent,
		handler::HandlerOutput,
		mock::{
			client_state::{MockClientState, MockConsensusState},
			context::{MockClientTypes, MockContext},
			header::MockHeader,
		},
		prelude::*,
		test_utils::get_dummy_account_id,
		Height,
	};
	use test_log::test;

	#[test]
	fn test_create_client_ok() {
		let ctx = MockContext::<MockClientTypes>::default();
		let signer = get_dummy_account_id();
		let height = Height::new(0, 42);

		let msg = MsgCreateAnyClient::new(
			MockClientState::new(MockHeader::new(height).into()).into(),
			MockConsensusState::new(MockHeader::new(height)).into(),
			signer,
		)
		.unwrap();

		let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

		match output {
			Ok(HandlerOutput { result, mut events, .. }) => {
				assert_eq!(events.len(), 1);
				let event = events.pop().unwrap();
				let expected_client_id = ClientId::new(&MockClientState::client_type(), 0).unwrap();
				assert!(
					matches!(event, IbcEvent::CreateClient(ref e) if e.client_id() == &expected_client_id)
				);
				assert_eq!(event.height(), ctx.host_height());
				match result {
					ClientResult::Create(create_result) => {
						assert_eq!(create_result.client_type, MockClientState::client_type());
						assert_eq!(create_result.client_id, expected_client_id);
						assert_eq!(create_result.client_state, msg.client_state);
						assert_eq!(create_result.consensus_state, msg.consensus_state);
					},
					_ => {
						panic!("unexpected result type: expected ClientResult::CreateResult!");
					},
				}
			},
			Err(err) => {
				panic!("unexpected error: {}", err);
			},
		}
	}

	#[test]
	fn test_create_client_ok_multiple() {
		let existing_client_id = ClientId::default();
		let signer = get_dummy_account_id();
		let height = Height::new(0, 80);

		let ctx = MockContext::default().with_client(&existing_client_id, height);

		let create_client_msgs: Vec<MsgCreateAnyClient<MockContext<MockClientTypes>>> = vec![
			MsgCreateAnyClient::new(
				MockClientState::new(
					MockHeader::new(Height { revision_height: 42, ..height }).into(),
				)
				.into(),
				MockConsensusState::new(MockHeader::new(Height { revision_height: 42, ..height }))
					.into(),
				signer.clone(),
			)
			.unwrap(),
			MsgCreateAnyClient::new(
				MockClientState::new(
					MockHeader::new(Height { revision_height: 42, ..height }).into(),
				)
				.into(),
				MockConsensusState::new(MockHeader::new(Height { revision_height: 42, ..height }))
					.into(),
				signer.clone(),
			)
			.unwrap(),
			MsgCreateAnyClient::new(
				MockClientState::new(
					MockHeader::new(Height { revision_height: 50, ..height }).into(),
				)
				.into(),
				MockConsensusState::new(MockHeader::new(Height { revision_height: 50, ..height }))
					.into(),
				signer,
			)
			.unwrap(),
		]
		.into_iter()
		.collect();

		// The expected client id that will be generated will be identical to "9999-mock-0" for all
		// tests. This is because we're not persisting any client results (which is done via the
		// tests for `ics26_routing::dispatch`.
		let expected_client_id = ClientId::new(&MockClientState::client_type(), 0).unwrap();

		for msg in create_client_msgs {
			let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

			match output {
				Ok(HandlerOutput { result, mut events, .. }) => {
					assert_eq!(events.len(), 1);
					let event = events.pop().unwrap();
					assert!(
						matches!(event, IbcEvent::CreateClient(ref e) if e.client_id() == &expected_client_id)
					);
					assert_eq!(event.height(), ctx.host_height());
					match result {
						ClientResult::Create(create_res) => {
							assert_eq!(create_res.client_type, msg.client_state.client_type());
							assert_eq!(create_res.client_id, expected_client_id);
							assert_eq!(create_res.client_state, msg.client_state);
							assert_eq!(create_res.consensus_state, msg.consensus_state);
						},
						_ => {
							panic!("expected result of type ClientResult::CreateResult");
						},
					}
				},
				Err(err) => {
					panic!("unexpected error: {}", err);
				},
			}
		}
	}
}
