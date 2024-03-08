use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTimeout as RawMsgChannelUpgradeTimeout;
use ibc_proto::Protobuf;

use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;
use crate::Height;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeTimeout";

/// Message definition the `ChanUpgradeTimeout` datagram.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeTimeout {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_channel: ChannelEnd,
    /// The proof of the counterparty channel
    pub proof_channel: CommitmentProofBytes,
    /// The height at which the proofs were queried.
    pub proof_height: Height,
    pub signer: Signer,
}

impl MsgChannelUpgradeTimeout {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        counterparty_channel: ChannelEnd,
        proof_channel: CommitmentProofBytes,
        proof_height: Height,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            counterparty_channel,
            proof_channel,
            proof_height,
            signer,
        }
    }
}

impl Msg for MsgChannelUpgradeTimeout {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeTimeout;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeTimeout> for MsgChannelUpgradeTimeout {}

impl TryFrom<RawMsgChannelUpgradeTimeout> for MsgChannelUpgradeTimeout {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeTimeout) -> Result<Self, Self::Error> {
        let raw_counterparty_channel = raw_msg
            .counterparty_channel
            .ok_or(Error::missing_channel())?;
        let counterparty_channel = ChannelEnd::try_from(raw_counterparty_channel)?;

        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeTimeout {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            counterparty_channel,
            proof_channel: raw_msg
                .proof_channel
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_height,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgChannelUpgradeTimeout> for RawMsgChannelUpgradeTimeout {
    fn from(domain_msg: MsgChannelUpgradeTimeout) -> Self {
        RawMsgChannelUpgradeTimeout {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            counterparty_channel: Some(domain_msg.counterparty_channel.into()),
            proof_channel: domain_msg.proof_channel.into(),
            proof_height: Some(domain_msg.proof_height.into()),
            signer: domain_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::core::ics04_channel::channel::test_util::get_dummy_raw_channel_end;
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTimeout as RawMsgChannelUpgradeTimeout;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeCnacel`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_timeout() -> RawMsgChannelUpgradeTimeout {
        RawMsgChannelUpgradeTimeout {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            counterparty_channel: Some(get_dummy_raw_channel_end()),
            proof_channel: get_dummy_proof(),
            proof_height: Some(RawHeight {
                revision_number: 1,
                revision_height: 1,
            }),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTimeout as RawMsgChannelUpgradeTimeout;
    use ibc_proto::ibc::core::client::v1::Height;

    use crate::core::ics04_channel::msgs::chan_upgrade_timeout::test_util::get_dummy_raw_msg_chan_upgrade_timeout;
    use crate::core::ics04_channel::msgs::chan_upgrade_timeout::MsgChannelUpgradeTimeout;

    #[test]
    fn parse_channel_upgrade_try_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeTimeout,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_timeout();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof channel".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    proof_channel: vec![],
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    proof_height: Some(Height {
                        revision_number: 0,
                        revision_height: 0,
                    }),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing proof height".to_string(),
                raw: RawMsgChannelUpgradeTimeout {
                    proof_height: None,
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeTimeout::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "RawMsgChannelUpgradeTimeout::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_timeout();
        let msg = MsgChannelUpgradeTimeout::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeTimeout::from(msg.clone());
        let msg_back = MsgChannelUpgradeTimeout::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
