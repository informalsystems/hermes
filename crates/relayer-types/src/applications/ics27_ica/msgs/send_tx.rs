use ibc_proto::{
    ibc::applications::interchain_accounts::controller::v1::MsgSendTx as RawMsgSendTx,
    Protobuf,
};
use serde_derive::{
    Deserialize,
    Serialize,
};

use crate::{
    applications::ics27_ica::{
        error::Error,
        packet_data::InterchainAccountPacketData,
    },
    core::ics24_host::{
        error::ValidationError,
        identifier::ConnectionId,
    },
    signer::Signer,
    timestamp::Timestamp,
    tx_msg::Msg,
};

pub const TYPE_URL: &str = "/ibc.applications.interchain_accounts.controller.v1.MsgSendTx";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MsgSendTx {
    pub owner: Signer,
    pub connection_id: ConnectionId,
    pub packet_data: InterchainAccountPacketData,
    pub relative_timeout: Timestamp,
}

impl Msg for MsgSendTx {
    type ValidationError = ValidationError;
    type Raw = RawMsgSendTx;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgSendTx> for MsgSendTx {}

impl TryFrom<RawMsgSendTx> for MsgSendTx {
    type Error = Error;

    fn try_from(value: RawMsgSendTx) -> Result<Self, Self::Error> {
        let relative_timeout = Timestamp::from_nanoseconds(value.relative_timeout)
            .map_err(|_| Error::invalid_relative_timeout(value.relative_timeout))?;
        let raw_packet_data = value
            .packet_data
            .ok_or(())
            .map_err(|_| Error::invalid_packet_data())?;
        Ok(MsgSendTx {
            owner: value.owner.parse().map_err(Error::owner)?,
            connection_id: value
                .connection_id
                .parse()
                .map_err(Error::invalid_connection_identifier)?,
            packet_data: raw_packet_data.try_into()?,
            relative_timeout,
        })
    }
}

impl From<MsgSendTx> for RawMsgSendTx {
    fn from(value: MsgSendTx) -> Self {
        RawMsgSendTx {
            owner: value.owner.to_string(),
            connection_id: value.connection_id.to_string(),
            packet_data: Some(value.packet_data.into()),
            relative_timeout: value.relative_timeout.nanoseconds(),
        }
    }
}
