use serde::{Deserialize, Serialize};

use ibc_proto::ibc::applications::interchain_accounts::controller::v1::MsgRegisterInterchainAccount as RawMsgRegisterInterchainAccount;
use ibc_proto::Protobuf;

use crate::applications::ics27_ica::error::Error;
use crate::core::ics04_channel::channel::Ordering;
use crate::core::ics04_channel::version::Version;
use crate::core::ics24_host::error::ValidationError;
use crate::core::ics24_host::identifier::ConnectionId;
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str =
    "/ibc.applications.interchain_accounts.controller.v1.MsgRegisterInterchainAccount";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MsgRegisterInterchainAccount {
    pub owner: Signer,
    pub connection_id: ConnectionId,
    pub version: Version,
    pub ordering: Ordering,
}

impl Msg for MsgRegisterInterchainAccount {
    type ValidationError = ValidationError;
    type Raw = RawMsgRegisterInterchainAccount;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgRegisterInterchainAccount> for MsgRegisterInterchainAccount {}

impl TryFrom<RawMsgRegisterInterchainAccount> for MsgRegisterInterchainAccount {
    type Error = Error;

    fn try_from(value: RawMsgRegisterInterchainAccount) -> Result<Self, Self::Error> {
        let chan_ordering = Ordering::from_i32(value.ordering).map_err(Error::ics04_channel)?;

        Ok(MsgRegisterInterchainAccount {
            owner: value.owner.parse().map_err(Error::owner)?,
            connection_id: value
                .connection_id
                .parse()
                .map_err(Error::invalid_connection_identifier)?,
            version: value.version.into(),
            ordering: chan_ordering,
        })
    }
}

impl From<MsgRegisterInterchainAccount> for RawMsgRegisterInterchainAccount {
    fn from(value: MsgRegisterInterchainAccount) -> Self {
        RawMsgRegisterInterchainAccount {
            owner: value.owner.to_string(),
            connection_id: value.connection_id.to_string(),
            version: value.version.to_string(),
            ordering: value.ordering as i32,
        }
    }
}
