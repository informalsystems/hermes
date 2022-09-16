//! Definition of domain type message `MsgUpdateAnyClient`.

use crate::prelude::*;
use core::fmt::Display;

use ibc_proto::google::protobuf::Any;
use tendermint_proto::Protobuf;

use crate::core::ics02_client::context::ClientKeeper;
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
pub struct MsgUpdateAnyClient<C: ClientKeeper> {
	pub client_id: ClientId,
	pub header: C::AnyHeader,
	pub signer: Signer,
}

impl<C> MsgUpdateAnyClient<C>
where
	C: ClientKeeper,
{
	pub fn new(client_id: ClientId, header: C::AnyHeader, signer: Signer) -> Self {
		MsgUpdateAnyClient { client_id, header, signer }
	}
}

impl<C> Msg for MsgUpdateAnyClient<C>
where
	C: ClientKeeper + Clone,
	C::AnyHeader: Clone,
	Any: From<C::AnyHeader>,
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
	C: ClientKeeper + Clone,
	C::AnyHeader: Clone,
	Any: From<C::AnyHeader>,
	MsgUpdateAnyClient<C>: TryFrom<MsgUpdateClient>,
	<MsgUpdateAnyClient<C> as TryFrom<MsgUpdateClient>>::Error: Display,
{
}

impl<C> TryFrom<RawMsgUpdateClient> for MsgUpdateAnyClient<C>
where
	C: ClientKeeper,
	C::AnyHeader: TryFrom<Any>,
	Error: From<<C::AnyHeader as TryFrom<Any>>::Error>,
{
	type Error = Error;

	fn try_from(raw: RawMsgUpdateClient) -> Result<Self, Self::Error> {
		let raw_header = raw.header.ok_or_else(Error::missing_raw_header)?;

		Ok(MsgUpdateAnyClient {
			client_id: raw.client_id.parse().map_err(Error::invalid_msg_update_client_id)?,
			header: C::AnyHeader::try_from(raw_header)?,
			signer: raw.signer.parse().map_err(Error::signer)?,
		})
	}
}

impl<C> From<MsgUpdateAnyClient<C>> for RawMsgUpdateClient
where
	C: ClientKeeper,
	Any: From<C::AnyHeader>,
{
	fn from(ics_msg: MsgUpdateAnyClient<C>) -> Self {
		RawMsgUpdateClient {
			client_id: ics_msg.client_id.to_string(),
			header: Some(ics_msg.header.into()),
			signer: ics_msg.signer.to_string(),
		}
	}
}

/*
#[cfg(test)]
mod tests {

	use test_log::test;

	use ibc_proto::ibc::core::client::v1::MsgUpdateClient;

	use crate::clients::ics07_tendermint::header::test_util::get_dummy_ics07_header;
	use crate::core::ics02_client::header::AnyHeader;
	use crate::core::ics02_client::msgs::MsgUpdateAnyClient;
	use crate::core::ics24_host::identifier::ClientId;
	use crate::mock::context::MockContext;
	use crate::test_utils::get_dummy_account_id;

	#[test]
	fn msg_update_client_serialization() {
		let client_id: ClientId = "tendermint".parse().unwrap();
		let signer = get_dummy_account_id();

		let header = get_dummy_ics07_header();

		let msg = MsgUpdateAnyClient::<MockContext>::new(
			client_id,
			AnyHeader::Tendermint(header),
			signer,
		);
		let raw = MsgUpdateClient::from(msg.clone());
		let msg_back = MsgUpdateAnyClient::try_from(raw.clone()).unwrap();
		let raw_back = MsgUpdateClient::from(msg_back.clone());
		assert_eq!(msg, msg_back);
		assert_eq!(raw, raw_back);
	}
}
 */
