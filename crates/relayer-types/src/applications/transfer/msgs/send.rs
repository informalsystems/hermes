use std::{
    fmt::Display,
    str::FromStr,
};

use ibc_proto::{
    cosmos::bank::v1beta1::MsgSend as RawMsgSend,
    Protobuf,
};
use serde_derive::{
    Deserialize,
    Serialize,
};

use crate::{
    applications::transfer::{
        error::Error,
        Coin,
    },
    core::ics24_host::error::ValidationError,
    tx_msg::Msg,
};

pub const TYPE_URL: &str = "/cosmos.bank.v1beta1.MsgSend";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgSend<D> {
    pub from_address: String,
    pub to_address: String,
    pub amount: Vec<Coin<D>>,
}

impl<D: Clone + Display> Msg for MsgSend<D> {
    type ValidationError = ValidationError;
    type Raw = RawMsgSend;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl<D: Clone + Display + FromStr> Protobuf<RawMsgSend> for MsgSend<D> where D::Err: Into<Error> {}

impl<D: FromStr> TryFrom<RawMsgSend> for MsgSend<D>
where
    D::Err: Into<Error>,
{
    type Error = Error;

    fn try_from(value: RawMsgSend) -> Result<Self, Self::Error> {
        let amount: Vec<Coin<D>> = value
            .amount
            .into_iter()
            .map(Coin::try_from)
            .collect::<Result<Vec<Coin<D>>, _>>()?;
        Ok(MsgSend {
            from_address: value.from_address,
            to_address: value.to_address,
            amount,
        })
    }
}

impl<D: Display> From<MsgSend<D>> for RawMsgSend {
    fn from(value: MsgSend<D>) -> Self {
        let amount = value.amount.into_iter().map(|coin| coin.into()).collect();
        RawMsgSend {
            from_address: value.from_address,
            to_address: value.to_address,
            amount,
        }
    }
}
