use std::convert::{TryFrom, TryInto};

use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::applications::transfer::v1::MsgTransfer as RawMsgTransfer;

use crate::address::{account_to_string, string_to_account};
use crate::application::ics20_fungible_token_transfer::error::{Error, Kind};
use crate::ics02_client::height::Height;
use crate::ics24_host::identifier::{ChannelId, PortId};
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
    pub sender: AccountId,
    /// the recipient address on the destination chain
    pub receiver: AccountId,
    /// Timeout height relative to the current block height.
    /// The timeout is disabled when set to 0.
    pub timeout_height: Height,
    /// Timeout timestamp (in nanoseconds) relative to the current block timestamp.
    /// The timeout is disabled when set to 0.
    pub timeout_timestamp: u64,
}

impl Msg for MsgTransfer {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.sender]
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
            sender: string_to_account(raw_msg.sender).unwrap(),
            receiver: string_to_account(raw_msg.receiver).unwrap(),
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
            sender: account_to_string(domain_msg.sender).unwrap(),
            receiver: account_to_string(domain_msg.receiver).unwrap(),
            timeout_height: Some(domain_msg.timeout_height.try_into().unwrap()),
            timeout_timestamp: 0,
        }
    }
}
