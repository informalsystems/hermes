//! Definition of domain type message `MsgCreateAnyClient`.

use crate::prelude::*;
use core::fmt::Display;

use ibc_proto::google::protobuf::Any;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::{MsgCreateClient as RawMsgCreateClient, MsgCreateClient};

use crate::{
	core::ics02_client::{context::ClientKeeper, error::Error},
	signer::Signer,
	tx_msg::Msg,
};

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgCreateClient";

/// A type of message that triggers the creation of a new on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgCreateAnyClient<C: ClientKeeper> {
	pub client_state: C::AnyClientState,
	pub consensus_state: C::AnyConsensusState,
	pub signer: Signer,
}

impl<C: ClientKeeper> MsgCreateAnyClient<C> {
	pub fn new(
		client_state: C::AnyClientState,
		consensus_state: C::AnyConsensusState,
		signer: Signer,
	) -> Result<Self, Error> {
		// if client_state.client_type() != consensus_state.client_type() {
		//     return Err(Error::raw_client_and_consensus_state_types_mismatch(
		//         client_state.client_type(),
		//         consensus_state.client_type(),
		//     ));
		// }

		Ok(MsgCreateAnyClient { client_state, consensus_state, signer })
	}
}

impl<C> Msg for MsgCreateAnyClient<C>
where
	C: ClientKeeper + Clone,
	Any: From<C::AnyClientState>,
	Any: From<C::AnyConsensusState>,
{
	type ValidationError = crate::core::ics24_host::error::ValidationError;
	type Raw = RawMsgCreateClient;

	fn route(&self) -> String {
		crate::keys::ROUTER_KEY.to_string()
	}

	fn type_url(&self) -> String {
		TYPE_URL.to_string()
	}
}

impl<C> Protobuf<RawMsgCreateClient> for MsgCreateAnyClient<C>
where
	C: ClientKeeper + Clone,
	Any: From<C::AnyClientState>,
	Any: From<C::AnyConsensusState>,
	MsgCreateAnyClient<C>: TryFrom<MsgCreateClient>,
	<MsgCreateAnyClient<C> as TryFrom<MsgCreateClient>>::Error: Display,
{
}

impl<C> TryFrom<RawMsgCreateClient> for MsgCreateAnyClient<C>
where
	C: ClientKeeper,
	C::AnyClientState: TryFrom<Any>,
	C::AnyConsensusState: TryFrom<Any>,
	Error: From<<C::AnyClientState as TryFrom<Any>>::Error>,
{
	type Error = Error;

	fn try_from(raw: RawMsgCreateClient) -> Result<Self, Error> {
		let raw_client_state = raw.client_state.ok_or_else(Error::missing_raw_client_state)?;

		let consensus_state = raw
			.consensus_state
			.and_then(|cs| C::AnyConsensusState::try_from(cs).ok())
			.ok_or_else(Error::missing_raw_consensus_state)?;

		MsgCreateAnyClient::new(
			C::AnyClientState::try_from(raw_client_state)?,
			consensus_state,
			raw.signer.parse().map_err(Error::signer)?,
		)
	}
}

impl<C> From<MsgCreateAnyClient<C>> for RawMsgCreateClient
where
	C: ClientKeeper,
	Any: From<C::AnyClientState>,
	Any: From<C::AnyConsensusState>,
{
	fn from(ics_msg: MsgCreateAnyClient<C>) -> Self {
		RawMsgCreateClient {
			client_state: Some(ics_msg.client_state.into()),
			consensus_state: Some(ics_msg.consensus_state.into()),
			signer: ics_msg.signer.to_string(),
		}
	}
}
