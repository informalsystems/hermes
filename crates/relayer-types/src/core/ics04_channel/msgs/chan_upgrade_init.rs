use crate::prelude::*;

use ibc_proto::protobuf::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeInit as RawMsgChannelUpgradeInit;

use crate::core::ics04_channel::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeInit";

/// Message definition for the first step in the channel 
/// upgrade handshake (`ChanUpgradeInit` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeInit {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub channel: ChannelEnd,
    pub signer: Signer,
}

impl MsgChannelUpgradeInit {
    pub fn new(port_id: PortId, channel_id: ChannelId, channel: ChannelEnd, signer: Signer) -> Self {
        Self {
            port_id,
            channel_id,
            signer,
        }
    }
}

impl Msg for MsgChannelUpgradeInit {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeInit;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeInit> for MsgChannelUpgradeInit {}

impl TryFrom<RawMsgChannelUpgradeInit> for MsgChannelUpgradeInit {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeInit) -> Result<Self, Self::Error> {
        Ok(MsgChannelUpgradeInit {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgChannelUpgradeInit> for RawMsgChannelUpgradeInit {
    fn from(domain_msg: MsgChannelUpgradeInit) -> Self {
        Self {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            signer: domain_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::prelude::*;
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeInit as RawMsgChannelUpgradeInit;

    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::get_dummy_bech32_account;

    /// Returns a dummy `RawMsgChannelUpgadeInit`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_init() -> RawMsgChannelUpgradeInit {
        RawMsgChannelUpgradeInit {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use test_log::test;

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeInit as RawMsgChannelUpgradeInit;

    use crate::core::ics04_channel::msgs::chan_upgrade_init::test_util::get_dummy_raw_msg_chan_upgrade_init;
    use crate::core::ics04_channel::msgs::chan_upgrade_init::MsgChannelUpgradeInit;

    #[test]
    fn parse_channel_upgrade_init_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeInit,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_init();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeInit {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeInit {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeInit {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
        ]
    }
}