//! This is the definition of a transfer messages that an application submits to a chain.

use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::apps::transfer::v1::MsgTransfer as RawMsgTransfer;
use tendermint_proto::Protobuf;

use crate::application::ics20_fungible_token_transfer::error::{Error, Kind};
use crate::ics02_client::height::Height;
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.applications.transfer.v1.MsgTransfer";

///
/// Message definition for the "packet receiving" datagram.
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgTransfer {
    /// the port on which the packet will be sent
    pub source_port: PortId,
    /// the channel by which the packet will be sent
    pub source_channel: ChannelId,
    /// the tokens to be transferred
    pub token: Option<ibc_proto::cosmos::base::v1beta1::Coin>,
    /// the sender address
    pub sender: Signer,
    /// the recipient address on the destination chain
    pub receiver: Signer,
    /// Timeout height relative to the current block height.
    /// The timeout is disabled when set to 0.
    pub timeout_height: Height,
    /// Timeout timestamp (in nanoseconds) relative to the current block timestamp.
    /// The timeout is disabled when set to 0.
    pub timeout_timestamp: u64,
}

impl Msg for MsgTransfer {
    type ValidationError = Error;
    type Raw = RawMsgTransfer;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgTransfer> for MsgTransfer {}

impl TryFrom<RawMsgTransfer> for MsgTransfer {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgTransfer) -> Result<Self, Self::Error> {
        Ok(MsgTransfer {
            source_port: raw_msg.source_port.parse().unwrap(),
            source_channel: raw_msg.source_channel.parse().unwrap(),
            token: raw_msg.token,
            sender: raw_msg.sender.into(),
            receiver: raw_msg.receiver.into(),
            timeout_height: raw_msg.timeout_height.unwrap().try_into().unwrap(),
            timeout_timestamp: 0,
        })
    }
}

impl From<MsgTransfer> for RawMsgTransfer {
    fn from(domain_msg: MsgTransfer) -> Self {
        RawMsgTransfer {
            source_port: domain_msg.source_port.to_string(),
            source_channel: domain_msg.source_channel.to_string(),
            token: domain_msg.token,
            sender: domain_msg.sender.to_string(),
            receiver: domain_msg.receiver.to_string(),
            timeout_height: Some(domain_msg.timeout_height.try_into().unwrap()),
            timeout_timestamp: 0,
        }
    }
}
