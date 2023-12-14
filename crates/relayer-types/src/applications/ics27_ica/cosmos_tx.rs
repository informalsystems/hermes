use ibc_proto::{
    google::protobuf::Any,
    ibc::applications::interchain_accounts::v1::CosmosTx as RawCosmosTx,
    Protobuf,
};
use serde_derive::{
    Deserialize,
    Serialize,
};

use crate::{
    applications::ics27_ica::error::Error,
    core::ics24_host::error::ValidationError,
    tx_msg::Msg,
};

pub const TYPE_URL: &str = "/ibc.applications.interchain_accounts.v1.CosmosTx";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CosmosTx {
    pub messages: Vec<Any>,
}

impl Msg for CosmosTx {
    type ValidationError = ValidationError;
    type Raw = RawCosmosTx;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawCosmosTx> for CosmosTx {}

impl TryFrom<RawCosmosTx> for CosmosTx {
    type Error = Error;

    fn try_from(value: RawCosmosTx) -> Result<Self, Self::Error> {
        Ok(CosmosTx {
            messages: value.messages,
        })
    }
}

impl From<CosmosTx> for RawCosmosTx {
    fn from(value: CosmosTx) -> Self {
        RawCosmosTx {
            messages: value.messages,
        }
    }
}
