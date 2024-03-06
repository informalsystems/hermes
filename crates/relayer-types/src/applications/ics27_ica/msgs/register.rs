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
        Ok(MsgRegisterInterchainAccount {
            owner: value.owner.parse().map_err(Error::owner)?,
            connection_id: value
                .connection_id
                .parse()
                .map_err(Error::invalid_connection_identifier)?,
            version: value.version.into(),
            ordering: Ordering::from_i32(value.ordering)
                .map_err(|_| Error::invalid_ordering(value.ordering))?,
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

#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LegacyRawMsgRegisterInterchainAccount {
    #[prost(string, tag = "1")]
    pub owner: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub connection_id: ::prost::alloc::string::String,
    #[prost(string, tag = "3")]
    pub version: ::prost::alloc::string::String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LegacyMsgRegisterInterchainAccount {
    pub owner: Signer,
    pub connection_id: ConnectionId,
    pub version: Version,
}

impl Msg for LegacyMsgRegisterInterchainAccount {
    type ValidationError = ValidationError;
    type Raw = LegacyRawMsgRegisterInterchainAccount;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<LegacyRawMsgRegisterInterchainAccount> for LegacyMsgRegisterInterchainAccount {}

impl TryFrom<LegacyRawMsgRegisterInterchainAccount> for LegacyMsgRegisterInterchainAccount {
    type Error = Error;

    fn try_from(value: LegacyRawMsgRegisterInterchainAccount) -> Result<Self, Self::Error> {
        Ok(LegacyMsgRegisterInterchainAccount {
            owner: value.owner.parse().map_err(Error::owner)?,
            connection_id: value
                .connection_id
                .parse()
                .map_err(Error::invalid_connection_identifier)?,
            version: value.version.into(),
        })
    }
}

impl From<LegacyMsgRegisterInterchainAccount> for LegacyRawMsgRegisterInterchainAccount {
    fn from(value: LegacyMsgRegisterInterchainAccount) -> Self {
        LegacyRawMsgRegisterInterchainAccount {
            owner: value.owner.to_string(),
            connection_id: value.connection_id.to_string(),
            version: value.version.to_string(),
        }
    }
}
