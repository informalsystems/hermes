//! Definition of domain type message `MsgUpdateAnyClient`.

use crate::prelude::*;
use core::fmt::Display;

use ibc_proto::google::protobuf::Any;
use tendermint_proto::Protobuf;

use crate::core::ics02_client::context::ClientTypes;
use ibc_proto::ibc::core::client::v1::{MsgUpdateClient as RawMsgUpdateClient, MsgUpdateClient};

use crate::core::ics02_client::error::Error;

use crate::{
	core::ics24_host::{error::ValidationError, identifier::ClientId},
	signer::Signer,
	tx_msg::Msg,
};

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpdateClient";

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
#[derive(Clone, Debug, PartialEq)] // TODO: Add Eq bound when possible
pub struct MsgUpdateAnyClient<C: ClientTypes> {
	pub client_id: ClientId,
	pub client_message: C::AnyClientMessage,
	pub signer: Signer,
}

impl<C> MsgUpdateAnyClient<C>
where
	C: ClientTypes,
{
	pub fn new(client_id: ClientId, client_message: C::AnyClientMessage, signer: Signer) -> Self {
		MsgUpdateAnyClient { client_id, client_message, signer }
	}
}

impl<C> Msg for MsgUpdateAnyClient<C>
where
	C: ClientTypes + Clone,
	C::AnyClientMessage: Clone,
	Any: From<C::AnyClientMessage>,
{
	type ValidationError = ValidationError;
	type Raw = RawMsgUpdateClient;

	fn route(&self) -> String {
		crate::keys::ROUTER_KEY.to_string()
	}

	fn type_url(&self) -> String {
		TYPE_URL.to_string()
	}
}

impl<C> Protobuf<RawMsgUpdateClient> for MsgUpdateAnyClient<C>
where
	C: ClientTypes + Clone,
	C::AnyClientMessage: Clone,
	Any: From<C::AnyClientMessage>,
	MsgUpdateAnyClient<C>: TryFrom<MsgUpdateClient>,
	<MsgUpdateAnyClient<C> as TryFrom<MsgUpdateClient>>::Error: Display,
{
}

impl<C> TryFrom<RawMsgUpdateClient> for MsgUpdateAnyClient<C>
where
	C: ClientTypes,
	C::AnyClientMessage: TryFrom<Any>,
	Error: From<<C::AnyClientMessage as TryFrom<Any>>::Error>,
{
	type Error = Error;

	fn try_from(raw: RawMsgUpdateClient) -> Result<Self, Self::Error> {
		let raw_client_message =
			raw.client_message.ok_or_else(Error::missing_raw_client_message)?;

		Ok(MsgUpdateAnyClient {
			client_id: raw.client_id.parse().map_err(Error::invalid_msg_update_client_id)?,
			client_message: C::AnyClientMessage::try_from(raw_client_message)?,
			signer: raw.signer.parse().map_err(Error::signer)?,
		})
	}
}

impl<C> From<MsgUpdateAnyClient<C>> for RawMsgUpdateClient
where
	C: ClientTypes,
	Any: From<C::AnyClientMessage>,
{
	fn from(ics_msg: MsgUpdateAnyClient<C>) -> Self {
		RawMsgUpdateClient {
			client_id: ics_msg.client_id.to_string(),
			client_message: Some(ics_msg.client_message.into()),
			signer: ics_msg.signer.to_string(),
		}
	}
}
