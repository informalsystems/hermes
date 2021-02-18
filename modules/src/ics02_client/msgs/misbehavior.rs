use std::convert::TryFrom;

use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::MsgSubmitMisbehaviour as RawMsgSubmitMisbehaviour;

use crate::address::{account_to_string, string_to_account};
use crate::ics02_client::client_misbehaviour::AnyMisbehaviour;
use crate::ics02_client::error::{Error, Kind};
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgSubmitMisbehaviour";

/// A type of message that submits client misbehaviour proof.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgSubmitAnyMisbehaviour {
    /// client unique identifier
    pub client_id: ClientId,
    /// misbehaviour used for freezing the light client
    pub misbehaviour: AnyMisbehaviour,
    /// signer address
    pub signer: AccountId,
}

impl Msg for MsgSubmitAnyMisbehaviour {
    type ValidationError = crate::ics24_host::error::ValidationError;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl Protobuf<RawMsgSubmitMisbehaviour> for MsgSubmitAnyMisbehaviour {}

impl TryFrom<RawMsgSubmitMisbehaviour> for MsgSubmitAnyMisbehaviour {
    type Error = Error;

    fn try_from(raw: RawMsgSubmitMisbehaviour) -> Result<Self, Self::Error> {
        let raw_misbehaviour = raw.misbehaviour.ok_or(Kind::InvalidRawMisbehaviour)?;
        let signer = string_to_account(raw.signer).map_err(|e| Kind::InvalidAddress.context(e))?;

        Ok(MsgSubmitAnyMisbehaviour {
            client_id: raw.client_id.parse().unwrap(),
            misbehaviour: AnyMisbehaviour::try_from(raw_misbehaviour).unwrap(),
            signer,
        })
    }
}

impl From<MsgSubmitAnyMisbehaviour> for RawMsgSubmitMisbehaviour {
    fn from(ics_msg: MsgSubmitAnyMisbehaviour) -> Self {
        RawMsgSubmitMisbehaviour {
            client_id: ics_msg.client_id.to_string(),
            misbehaviour: Some(ics_msg.misbehaviour.into()),
            signer: account_to_string(ics_msg.signer).unwrap(),
        }
    }
}
