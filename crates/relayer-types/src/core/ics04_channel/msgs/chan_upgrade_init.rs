use crate::timestamp::Timestamp;
use crate::{prelude::*, Height};

use ibc_proto::protobuf::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeInit as RawMsgChannelUpgradeInit;

use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeInit";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UpgradeTimeout {
    /// Timeout height indicates the height at which the counterparty
    /// must no longer proceed with the upgrade handshake.
    /// The chains will then preserve their original channel and the upgrade handshake is aborted
    Height(Height),

    /// Timeout timestamp indicates the time on the counterparty at which
    /// the counterparty must no longer proceed with the upgrade handshake.
    /// The chains will then preserve their original channel and the upgrade handshake is aborted.
    Timestamp(Timestamp),

    /// Both timeouts are set.
    Both(Height, Timestamp),
}

impl UpgradeTimeout {
    pub fn new(height: Option<Height>, timestamp: Option<Timestamp>) -> Result<Self, Error> {
        match (height, timestamp) {
            (Some(height), None) => Ok(UpgradeTimeout::Height(height)),
            (None, Some(timestamp)) => Ok(UpgradeTimeout::Timestamp(timestamp)),
            (Some(height), Some(timestamp)) => Ok(UpgradeTimeout::Both(height, timestamp)),
            (None, None) => Err(Error::missing_upgrade_timeout()),
        }
    }

    pub fn into_tuple(self) -> (Option<Height>, Option<Timestamp>) {
        match self {
            UpgradeTimeout::Height(height) => (Some(height), None),
            UpgradeTimeout::Timestamp(timestamp) => (None, Some(timestamp)),
            UpgradeTimeout::Both(height, timestamp) => (Some(height), Some(timestamp)),
        }
    }
}

/// Message definition for the first step in the channel
/// upgrade handshake (`ChanUpgradeInit` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeInit {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub proposed_upgrade_channel: ChannelEnd,
    pub timeout: UpgradeTimeout,
    pub signer: Signer,
}

impl MsgChannelUpgradeInit {
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        proposed_upgrade_channel: ChannelEnd,
        timeout: UpgradeTimeout,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            proposed_upgrade_channel,
            timeout,
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
        let proposed_upgrade_channel: ChannelEnd = raw_msg
            .proposed_upgrade_channel
            .ok_or_else(Error::missing_proposed_upgrade_channel)?
            .try_into()?;

        let timeout_height = raw_msg
            .timeout_height
            .map(Height::try_from)
            .transpose()
            .map_err(|_| Error::invalid_timeout_height())?;

        let timeout_timestamp = Some(raw_msg.timeout_timestamp)
            .filter(|&ts| ts != 0)
            .map(|raw_ts| {
                Timestamp::from_nanoseconds(raw_ts).map_err(Error::invalid_timeout_timestamp)
            })
            .transpose()?;

        let timeout = UpgradeTimeout::new(timeout_height, timeout_timestamp)?;

        Ok(MsgChannelUpgradeInit {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
            proposed_upgrade_channel,
            timeout,
        })
    }
}

impl From<MsgChannelUpgradeInit> for RawMsgChannelUpgradeInit {
    fn from(domain_msg: MsgChannelUpgradeInit) -> Self {
        let (timeout_height, timeout_timestamp) = domain_msg.timeout.into_tuple();

        Self {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            signer: domain_msg.signer.to_string(),
            proposed_upgrade_channel: Some(domain_msg.proposed_upgrade_channel.into()),
            timeout_height: timeout_height.map(Into::into),
            timeout_timestamp: timeout_timestamp.map(|ts| ts.nanoseconds()).unwrap_or(0),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeInit as RawMsgChannelUpgradeInit;

    use crate::core::ics02_client::height::Height;
    use crate::core::ics04_channel::channel::test_util::get_dummy_raw_channel_end;
    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::prelude::*;
    use crate::test_utils::get_dummy_bech32_account;
    use crate::timestamp::Timestamp;

    /// Returns a dummy `RawMsgChannelUpgadeInit`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_init() -> RawMsgChannelUpgradeInit {
        RawMsgChannelUpgradeInit {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            signer: get_dummy_bech32_account(),
            proposed_upgrade_channel: Some(get_dummy_raw_channel_end()),
            timeout_height: Some(Height::new(0, 10).unwrap().into()),
            timeout_timestamp: Timestamp::now().nanoseconds(),
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
                name: "Correct port ID".to_string(),
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
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeInit {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeInit {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeInit {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeInit::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "MsgChannelUpgradeInit::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_init();
        let msg = MsgChannelUpgradeInit::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeInit::from(msg.clone());
        let msg_back = MsgChannelUpgradeInit::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
