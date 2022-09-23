//! Protocol logic specific to processing ICS2 messages of type `MsgUpgradeAnyClient`.

use crate::core::ics02_client::context::ClientTypes;
use crate::{
	core::{
		ics02_client::{
			client_def::{ClientDef, ConsensusUpdateResult},
			client_state::ClientState,
			error::Error,
			events::Attributes,
			handler::ClientResult,
			msgs::upgrade_client::MsgUpgradeAnyClient,
		},
		ics24_host::identifier::ClientId,
		ics26_routing::context::ReaderContext,
	},
	events::IbcEvent,
	handler::{HandlerOutput, HandlerResult},
	prelude::*,
};
use core::fmt::Debug;

/// The result following the successful processing of a `MsgUpgradeAnyClient` message.
/// This data type should be used with a qualified name `upgrade_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result<C: ClientTypes> {
	pub client_id: ClientId,
	pub client_state: C::AnyClientState,
	pub consensus_state: Option<ConsensusUpdateResult<C>>,
}

pub fn process<Ctx>(
	ctx: &Ctx,
	msg: MsgUpgradeAnyClient<Ctx>,
) -> HandlerResult<ClientResult<Ctx>, Error>
where
	Ctx: ReaderContext + Eq + Debug + Clone,
{
	let mut output = HandlerOutput::builder();
	let MsgUpgradeAnyClient { client_id, .. } = msg;

	// Read client state from the host chain store.
	let client_state = ctx.client_state(&client_id)?;

	if client_state.is_frozen() {
		return Err(Error::client_frozen(client_id));
	}

	let upgrade_client_state = msg.client_state.clone();

	if client_state.latest_height() >= upgrade_client_state.latest_height() {
		return Err(Error::low_upgrade_height(
			client_state.latest_height(),
			upgrade_client_state.latest_height(),
		));
	}

	let client_type = ctx.client_type(&client_id)?;

	let client_def = client_state.client_def();

	let (new_client_state, new_consensus_state) = client_def
		.verify_upgrade_and_update_state::<Ctx>(
			&upgrade_client_state,
			&msg.consensus_state,
			msg.proof_upgrade_client.clone(),
			msg.proof_upgrade_consensus_state,
		)?;

	// Not implemented yet: https://github.com/informalsystems/ibc-rs/issues/722
	// todo!()
	let event_attributes = Attributes {
		client_id: client_id.clone(),
		height: ctx.host_height(),
		client_type: client_type.to_owned(),
		consensus_height: new_client_state.latest_height(),
	};

	let result = ClientResult::Upgrade(Result {
		client_id,
		client_state: new_client_state,
		consensus_state: Some(new_consensus_state),
	});

	output.emit(IbcEvent::UpgradeClient(event_attributes.into()));
	Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	use core::str::FromStr;

	use crate::{
		core::{
			ics02_client::{
				client_state::ClientState,
				context::ClientReader,
				error::{Error, ErrorDetail},
				handler::{dispatch, ClientResult::Upgrade},
				msgs::{upgrade_client::MsgUpgradeAnyClient, ClientMsg},
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
		test_utils::get_dummy_account_id,
		Height,
	};

	#[test]
	fn test_upgrade_client_ok() {
		let client_id = ClientId::default();
		let signer = get_dummy_account_id();

		let ctx =
			MockContext::<MockClientTypes>::default().with_client(&client_id, Height::new(0, 42));

		let msg = MsgUpgradeAnyClient {
			client_id: client_id.clone(),
			client_state: MockClientState::new(MockHeader::new(Height::new(1, 26)).into()).into(),
			consensus_state: MockConsensusState::new(MockHeader::new(Height::new(1, 26))).into(),
			proof_upgrade_client: Default::default(),
			proof_upgrade_consensus_state: Default::default(),
			signer,
		};

		let output = dispatch(&ctx, ClientMsg::UpgradeClient(msg.clone()));

		match output {
			Ok(HandlerOutput { result, mut events, log }) => {
				assert_eq!(events.len(), 1);
				let event = events.pop().unwrap();
				assert!(
					matches!(event, IbcEvent::UpgradeClient(ref e) if e.client_id() == &msg.client_id)
				);
				assert_eq!(event.height(), ctx.host_height());
				assert!(log.is_empty());
				// Check the result
				match result {
					Upgrade(upg_res) => {
						assert_eq!(upg_res.client_id, client_id);
						assert_eq!(upg_res.client_state, msg.client_state)
					},
					_ => panic!("upgrade handler result has incorrect type"),
				}
			},
			Err(err) => {
				panic!("unexpected error: {}", err);
			},
		}
	}

	#[test]
	fn test_upgrade_nonexisting_client() {
		let client_id = ClientId::from_str("mockclient1").unwrap();
		let signer = get_dummy_account_id();

		let ctx =
			MockContext::<MockClientTypes>::default().with_client(&client_id, Height::new(0, 42));

		let msg = MsgUpgradeAnyClient {
			client_id: ClientId::from_str("nonexistingclient").unwrap(),
			client_state: MockClientState::new(MockHeader::new(Height::new(1, 26).into()).into())
				.into(),
			consensus_state: MockConsensusState::new(MockHeader::new(Height::new(1, 26))).into(),
			proof_upgrade_client: Default::default(),
			proof_upgrade_consensus_state: Default::default(),
			signer,
		};

		let output = dispatch(&ctx, ClientMsg::UpgradeClient(msg.clone()));

		match output {
			Err(Error(ErrorDetail::ClientNotFound(e), _)) => {
				assert_eq!(e.client_id, msg.client_id);
			},
			_ => {
				panic!("expected ClientNotFound error, instead got {:?}", output);
			},
		}
	}

	#[test]
	fn test_upgrade_client_low_height() {
		let client_id = ClientId::default();
		let signer = get_dummy_account_id();

		let ctx =
			MockContext::<MockClientTypes>::default().with_client(&client_id, Height::new(0, 42));

		let msg = MsgUpgradeAnyClient {
			client_id,
			client_state: MockClientState::new(MockHeader::new(Height::new(0, 26)).into()).into(),
			consensus_state: MockConsensusState::new(MockHeader::new(Height::new(0, 26))).into(),
			proof_upgrade_client: Default::default(),
			proof_upgrade_consensus_state: Default::default(),
			signer,
		};

		let output = dispatch(&ctx, ClientMsg::UpgradeClient(msg.clone()));

		match output {
			Err(Error(ErrorDetail::LowUpgradeHeight(e), _)) => {
				assert_eq!(e.upgraded_height, Height::new(0, 42));
				assert_eq!(e.client_height, msg.client_state.latest_height());
			},
			_ => {
				panic!("expected LowUpgradeHeight error, instead got {:?}", output);
			},
		}
	}
}
