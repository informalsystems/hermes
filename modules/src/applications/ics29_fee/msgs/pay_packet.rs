use ibc_proto::ibc::applications::fee::v1::MsgPayPacketFee;

use crate::prelude::*;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.applications.transfer.v1.MsgTransfer";

pub enum Error {}

impl Msg for MsgPayPacketFee {
    type ValidationError = Error;
    type Raw = MsgPayPacketFee;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}
