use ibc_proto::ibc::{
    applications::interchain_accounts::v1::InterchainAccountPacketData as RawInterchainAccountPacketData,
    apps::interchain_accounts::v1::Type,
};
use serde_derive::{Deserialize, Serialize};

use crate::applications::ics27_ica::error::Error;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterchainAccountPacketData {
    pub r#type: i32,
    pub data: Vec<u8>,
    pub memo: String,
}

impl InterchainAccountPacketData {
    pub fn new(data: Vec<u8>) -> Self {
        InterchainAccountPacketData {
            r#type: Type::ExecuteTx.into(),
            data,
            memo: String::default(),
        }
    }
}

impl TryFrom<RawInterchainAccountPacketData> for InterchainAccountPacketData {
    type Error = Error;

    fn try_from(value: RawInterchainAccountPacketData) -> Result<Self, Self::Error> {
        Ok(InterchainAccountPacketData {
            r#type: value.r#type,
            data: value.data,
            memo: value.memo,
        })
    }
}

impl From<InterchainAccountPacketData> for RawInterchainAccountPacketData {
    fn from(value: InterchainAccountPacketData) -> Self {
        RawInterchainAccountPacketData {
            r#type: value.r#type,
            data: value.data,
            memo: value.memo,
        }
    }
}
