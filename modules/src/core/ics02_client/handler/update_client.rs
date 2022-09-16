//! Protocol logic specific to processing ICS2 messages of type `MsgUpdateAnyClient`.
use core::fmt::Debug;

use crate::{
	core::{
		ics02_client::{
			client_consensus::ConsensusState,
			client_def::{ClientDef, ConsensusUpdateResult},
			client_state::ClientState,
			context::ClientKeeper,
			error::Error,
			events::Attributes,
			handler::ClientResult,
			height::Height,
			msgs::update_client::MsgUpdateAnyClient,
		},
		ics24_host::identifier::ClientId,
		ics26_routing::context::ReaderContext,
	},
	events::IbcEvent,
	handler::{HandlerOutput, HandlerResult},
	prelude::*,
	timestamp::Timestamp,
};

/// The result following the successful processing of a `MsgUpdateAnyClient` message. Preferably
/// this data type should be used with a qualified name `update_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result<C: ClientKeeper> {
	pub client_id: ClientId,
	pub client_state: C::AnyClientState,
	pub consensus_state: Option<ConsensusUpdateResult<C>>,
	pub processed_time: Timestamp,
	pub processed_height: Height,
}

pub fn process<Ctx>(
	ctx: &Ctx,
	msg: MsgUpdateAnyClient<Ctx>,
) -> HandlerResult<ClientResult<Ctx>, Error>
where
	Ctx: ReaderContext,
{
	let mut output = HandlerOutput::builder();

	let MsgUpdateAnyClient { client_id, header, signer: _ } = msg;

	// Read client type from the host chain store. The client should already exist.
	let client_type = ctx.client_type(&client_id)?;

	// Read client state from the host chain store.
	let client_state = ctx.client_state(&client_id)?;

	let client_def = client_state.client_def();

	if client_state.is_frozen() {
		return Err(Error::client_frozen(client_id))
	}

	// Read consensus state from the host chain store.
	let latest_consensus_state =
		ctx.consensus_state(&client_id, client_state.latest_height()).map_err(|_| {
			Error::consensus_state_not_found(client_id.clone(), client_state.latest_height())
		})?;

	tracing::debug!("latest consensus state: {:?}", latest_consensus_state);

	let now = ctx.host_timestamp();
	let duration = now.duration_since(&latest_consensus_state.timestamp()).ok_or_else(|| {
		Error::invalid_consensus_state_timestamp(latest_consensus_state.timestamp(), now)
	})?;

	if client_state.expired(duration) {
		return Err(Error::header_not_within_trust_period(latest_consensus_state.timestamp(), now))
	}

	client_def
		.verify_header::<Ctx>(ctx, client_id.clone(), client_state.clone(), header.clone())
		.map_err(|e| Error::header_verification_failure(e.to_string()))?;

	let found_misbehaviour = client_def
		.check_for_misbehaviour(ctx, client_id.clone(), client_state.clone(), header.clone())
		.map_err(|e| Error::header_verification_failure(e.to_string()))?;

	let event_attributes = Attributes {
		client_id: client_id.clone(),
		height: ctx.host_height(),
		client_type: client_type.to_owned(),
		consensus_height: client_state.latest_height(),
	};

	if found_misbehaviour {
		let client_state = client_def.update_state_on_misbehaviour(client_state, header)?;
		let result = ClientResult::Update(Result {
			client_id,
			client_state,
			consensus_state: None,
			processed_time: ctx.host_timestamp(),
			processed_height: ctx.host_height(),
		});
		output.emit(IbcEvent::ClientMisbehaviour(event_attributes.into()));
		return Ok(output.with_result(result))
	}
	// Use client_state to validate the new header against the latest consensus_state.
	// This function will return the new client_state (its latest_height changed) and a
	// consensus_state obtained from header. These will be later persisted by the keeper.
	let (new_client_state, new_consensus_state) = client_def
		.update_state(ctx, client_id.clone(), client_state, header)
		.map_err(|e| Error::header_verification_failure(e.to_string()))?;

	let result = ClientResult::<Ctx>::Update(Result {
		client_id,
		client_state: new_client_state,
		consensus_state: Some(new_consensus_state),
		processed_time: ctx.host_timestamp(),
		processed_height: ctx.host_height(),
	});

	output.emit(IbcEvent::UpdateClient(event_attributes.into()));

	Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
	use core::str::FromStr;
	use test_log::test;

	use crate::{
		core::{
			ics02_client::{
				context::ClientReader,
				error::{Error, ErrorDetail},
				handler::{dispatch, ClientResult::Update},
				header::Header,
				msgs::{update_client::MsgUpdateAnyClient, ClientMsg},
			},
			ics24_host::identifier::ClientId,
		},
		events::IbcEvent,
		handler::HandlerOutput,
		mock::{
			client_state::{AnyClientState, MockClientState},
			context::{MockClientTypes, MockContext},
			header::MockHeader,
		},
		prelude::*,
		test_utils::get_dummy_account_id,
		timestamp::Timestamp,
		Height,
	};

	#[test]
	fn test_update_client_ok() {
		let client_id = ClientId::default();
		let signer = get_dummy_account_id();

		let timestamp = Timestamp::now();

		let ctx =
			MockContext::<MockClientTypes>::default().with_client(&client_id, Height::new(0, 42));
		let msg = MsgUpdateAnyClient {
			client_id: client_id.clone(),
			header: MockHeader::new(Height::new(0, 46)).with_timestamp(timestamp).into(),
			signer,
		};

		let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

		match output {
			Ok(HandlerOutput { result, mut events, log }) => {
				assert_eq!(events.len(), 1);
				let event = events.pop().unwrap();
				assert!(
					matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
				);
				assert_eq!(event.height(), ctx.host_height());
				assert!(log.is_empty());
				// Check the result
				match result {
					Update(upd_res) => {
						assert_eq!(upd_res.client_id, client_id);
						assert_eq!(
							upd_res.client_state,
							AnyClientState::Mock(MockClientState::new(
								MockHeader::new(msg.header.height()).with_timestamp(timestamp)
							))
						)
					},
					_ => panic!("update handler result has incorrect type"),
				}
			},
			Err(err) => {
				panic!("unexpected error: {}", err);
			},
		}
	}

	#[test]
	fn test_update_nonexisting_client() {
		let client_id = ClientId::from_str("mockclient1").unwrap();
		let signer = get_dummy_account_id();

		let ctx =
			MockContext::<MockClientTypes>::default().with_client(&client_id, Height::new(0, 42));

		let msg = MsgUpdateAnyClient {
			client_id: ClientId::from_str("nonexistingclient").unwrap(),
			header: MockHeader::new(Height::new(0, 46)).into(),
			signer,
		};

		let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

		match output {
			Err(Error(ErrorDetail::ClientNotFound(e), _)) => {
				assert_eq!(e.client_id, msg.client_id);
			},
			_ => {
				panic!("expected ClientNotFound error, instead got {:?}", output)
			},
		}
	}

	#[test]
	fn test_update_client_ok_multiple() {
		let client_ids = vec![
			ClientId::from_str("mockclient1").unwrap(),
			ClientId::from_str("mockclient2").unwrap(),
			ClientId::from_str("mockclient3").unwrap(),
		];
		let signer = get_dummy_account_id();
		let initial_height = Height::new(0, 45);
		let update_height = Height::new(0, 49);

		let mut ctx = MockContext::<MockClientTypes>::default();

		for cid in &client_ids {
			ctx = ctx.with_client(cid, initial_height);
		}

		for cid in &client_ids {
			let msg = MsgUpdateAnyClient {
				client_id: cid.clone(),
				header: MockHeader::new(update_height).into(),
				signer: signer.clone(),
			};

			let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

			match output {
				Ok(HandlerOutput { result: _, mut events, log }) => {
					assert_eq!(events.len(), 1);
					let event = events.pop().unwrap();
					assert!(
						matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
					);
					assert_eq!(event.height(), ctx.host_height());
					assert!(log.is_empty());
				},
				Err(err) => {
					panic!("unexpected error: {}", err);
				},
			}
		}
	}
}
