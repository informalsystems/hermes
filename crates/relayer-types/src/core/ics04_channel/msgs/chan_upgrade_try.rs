use crate::timestamp::Timestamp;
use crate::{prelude::*, Height};

use ibc_proto::protobuf::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::timeout::UpgradeTimeout;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeTry";

/// Message definition for the second step of the channel upgrade
/// handshake (the `ChanUpgradeTry` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeTry {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub signer: Signer,
    pub counterparty_channel: ChannelEnd,
    pub counterparty_sequence: u64,
    pub proposed_upgrade_channel: ChannelEnd,
    pub timeout: UpgradeTimeout,
    pub proof_channel: CommitmentProofBytes,
    pub proof_upgrade_timeout: CommitmentProofBytes,
    pub proof_upgrade_sequence: CommitmentProofBytes,
    pub proof_height: Height,
}

impl MsgChannelUpgradeTry {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        signer: Signer,
        counterparty_channel: ChannelEnd,
        proposed_upgrade_channel: ChannelEnd,
        counterparty_sequence: u64,
        timeout: UpgradeTimeout,
        proof_channel: CommitmentProofBytes,
        proof_upgrade_timeout: CommitmentProofBytes,
        proof_upgrade_sequence: CommitmentProofBytes,
        proof_height: Height,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            signer,
            counterparty_channel,
            counterparty_sequence,
            proposed_upgrade_channel,
            timeout,
            proof_channel,
            proof_upgrade_timeout,
            proof_upgrade_sequence,
            proof_height,
        }
    }
}

impl Msg for MsgChannelUpgradeTry {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeTry;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeTry> for MsgChannelUpgradeTry {}

impl TryFrom<RawMsgChannelUpgradeTry> for MsgChannelUpgradeTry {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeTry) -> Result<Self, Self::Error> {
        let counterparty_channel = raw_msg
            .counterparty_channel
            .ok_or_else(Error::missing_channel)?
            .try_into()?;

        let proposed_upgrade_channel = raw_msg
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

        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeTry {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
            counterparty_channel,
            proposed_upgrade_channel,
            counterparty_sequence: raw_msg.counterparty_sequence,
            timeout,
            proof_channel: raw_msg
                .proof_channel
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_upgrade_timeout: raw_msg
                .proof_upgrade_timeout
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_upgrade_sequence: raw_msg
                .proof_upgrade_sequence
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_height,
        })
    }
}

impl From<MsgChannelUpgradeTry> for RawMsgChannelUpgradeTry {
    fn from(domain_msg: MsgChannelUpgradeTry) -> Self {
        let (timeout_height, timeout_timestamp) = domain_msg.timeout.into_tuple();

        RawMsgChannelUpgradeTry {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            signer: domain_msg.signer.to_string(),
            counterparty_channel: Some(domain_msg.counterparty_channel.into()),
            counterparty_sequence: domain_msg.counterparty_sequence,
            proposed_upgrade_channel: Some(domain_msg.proposed_upgrade_channel.into()),
            timeout_height: timeout_height.map(Into::into),
            timeout_timestamp: timeout_timestamp.map(|ts| ts.nanoseconds()).unwrap_or(0),
            proof_channel: domain_msg.proof_channel.into(),
            proof_upgrade_timeout: domain_msg.proof_upgrade_timeout.into(),
            proof_upgrade_sequence: domain_msg.proof_upgrade_sequence.into(),
            proof_height: Some(domain_msg.proof_height.into()),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;
    use ibc_proto::ibc::core::client::v1::Height;

    use crate::core::ics04_channel::channel::test_util::get_dummy_raw_channel_end;
    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::prelude::*;
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeTry`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_try() -> RawMsgChannelUpgradeTry {
        RawMsgChannelUpgradeTry {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            signer: get_dummy_bech32_account(),
            counterparty_channel: Some(get_dummy_raw_channel_end()),
            counterparty_sequence: 1,
            proposed_upgrade_channel: Some(get_dummy_raw_channel_end()),
            timeout_height: Some(Height {
                revision_number: 1,
                revision_height: 1,
            }),
            timeout_timestamp: 1681737922,
            proof_channel: get_dummy_proof(),
            proof_upgrade_timeout: get_dummy_proof(),
            proof_upgrade_sequence: get_dummy_proof(),
            proof_height: Some(Height {
                revision_number: 1,
                revision_height: 1,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use test_log::test;

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

    use crate::core::ics04_channel::msgs::chan_upgrade_try::test_util::get_dummy_raw_msg_chan_upgrade_try;
    use crate::core::ics04_channel::msgs::chan_upgrade_try::MsgChannelUpgradeTry;

    #[test]
    fn parse_channel_upgrade_init_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeTry,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_try();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof channel".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    proof_channel: vec![],
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof upgrade timeout".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    proof_upgrade_timeout: vec![],
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof upgrade sequence".to_string(),
                raw: RawMsgChannelUpgradeTry {
                    proof_upgrade_sequence: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            }
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeTry::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "MsgChannelUpgradeTry::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_try();
        let msg = MsgChannelUpgradeTry::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeTry::from(msg.clone());
        let msg_back = MsgChannelUpgradeTry::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
