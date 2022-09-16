use crate::prelude::*;
use core::fmt::Display;

use crate::core::ics02_client::context::ClientKeeper;
use ibc_proto::{
	google::protobuf::Any, ibc::core::client::v1::MsgSubmitMisbehaviour as RawMsgSubmitMisbehaviour,
};
use tendermint_proto::Protobuf;

use crate::{
	core::{ics02_client::error::Error, ics24_host::identifier::ClientId},
	signer::Signer,
	tx_msg::Msg,
};

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgSubmitMisbehaviour";

/// A type of message that submits client misbehaviour proof.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgSubmitAnyMisbehaviour<C: ClientKeeper> {
	/// client unique identifier
	pub client_id: ClientId,
	/// misbehaviour used for freezing the light client
	pub misbehaviour: C::AnyMisbehaviour,
	/// signer address
	pub signer: Signer,
}

impl<C: ClientKeeper> Msg for MsgSubmitAnyMisbehaviour<C>
where
	Any: From<C::AnyMisbehaviour>,
{
	type ValidationError = crate::core::ics24_host::error::ValidationError;
	type Raw = RawMsgSubmitMisbehaviour;

	fn route(&self) -> String {
		crate::keys::ROUTER_KEY.to_string()
	}

	fn type_url(&self) -> String {
		TYPE_URL.to_string()
	}
}

impl<C: ClientKeeper> Protobuf<RawMsgSubmitMisbehaviour> for MsgSubmitAnyMisbehaviour<C>
where
	Any: From<C::AnyMisbehaviour>,
	MsgSubmitAnyMisbehaviour<C>: TryFrom<RawMsgSubmitMisbehaviour>,
	<MsgSubmitAnyMisbehaviour<C> as TryFrom<RawMsgSubmitMisbehaviour>>::Error: Display,
{
}

impl<C: ClientKeeper> TryFrom<RawMsgSubmitMisbehaviour> for MsgSubmitAnyMisbehaviour<C>
where
	C::AnyMisbehaviour: TryFrom<Any>,
	Error: From<<C::AnyMisbehaviour as TryFrom<Any>>::Error>,
{
	type Error = Error;

	fn try_from(raw: RawMsgSubmitMisbehaviour) -> Result<Self, Self::Error> {
		let raw_misbehaviour = raw.misbehaviour.ok_or_else(Error::missing_raw_misbehaviour)?;

		Ok(MsgSubmitAnyMisbehaviour {
			client_id: raw.client_id.parse().map_err(Error::invalid_raw_misbehaviour)?,
			misbehaviour: C::AnyMisbehaviour::try_from(raw_misbehaviour)?,
			signer: raw.signer.parse().map_err(Error::signer)?,
		})
	}
}

impl<C: ClientKeeper> From<MsgSubmitAnyMisbehaviour<C>> for RawMsgSubmitMisbehaviour
where
	Any: From<C::AnyMisbehaviour>,
{
	fn from(ics_msg: MsgSubmitAnyMisbehaviour<C>) -> Self {
		RawMsgSubmitMisbehaviour {
			client_id: ics_msg.client_id.to_string(),
			misbehaviour: Some(ics_msg.misbehaviour.into()),
			signer: ics_msg.signer.to_string(),
		}
	}
}
