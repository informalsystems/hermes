use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeAck as RawMsgChannelUpgradeAck;
use ibc_proto::Protobuf;

use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::upgrade::Upgrade;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;
use crate::Height;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeAck";

/// Message definition for the third step of the channel upgrade
/// handshake (the `ChanUpgradeAck` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeAck {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_upgrade: Upgrade,
    /// The proof of the counterparty channel
    pub proof_channel: CommitmentProofBytes,
    /// The proof of the counterparty upgrade
    pub proof_upgrade: CommitmentProofBytes,
    /// The height at which the proofs were queried.
    pub proof_height: Height,
    pub signer: Signer,
}

impl MsgChannelUpgradeAck {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        counterparty_upgrade: Upgrade,
        proof_channel: CommitmentProofBytes,
        proof_upgrade: CommitmentProofBytes,
        proof_height: Height,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            counterparty_upgrade,
            proof_channel,
            proof_upgrade,
            proof_height,
            signer,
        }
    }
}

impl Msg for MsgChannelUpgradeAck {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeAck;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeAck> for MsgChannelUpgradeAck {}

impl TryFrom<RawMsgChannelUpgradeAck> for MsgChannelUpgradeAck {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeAck) -> Result<Self, Self::Error> {
        let counterparty_upgrade = raw_msg
            .counterparty_upgrade
            .ok_or(Error::missing_upgrade())?
            .try_into()?;

        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeAck {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            counterparty_upgrade,
            proof_channel: raw_msg
                .proof_channel
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_upgrade: raw_msg
                .proof_upgrade
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_height,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgChannelUpgradeAck> for RawMsgChannelUpgradeAck {
    fn from(domain_msg: MsgChannelUpgradeAck) -> Self {
        RawMsgChannelUpgradeAck {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            counterparty_upgrade: Some(domain_msg.counterparty_upgrade.into()),
            proof_upgrade: domain_msg.proof_upgrade.into(),
            proof_channel: domain_msg.proof_channel.into(),
            proof_height: Some(domain_msg.proof_height.into()),
            signer: domain_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeAck as RawMsgChannelUpgradeAck;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics04_channel::upgrade::test_util::get_dummy_upgrade;
    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeAck`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_ack() -> RawMsgChannelUpgradeAck {
        RawMsgChannelUpgradeAck {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            counterparty_upgrade: Some(get_dummy_upgrade()),
            proof_upgrade: get_dummy_proof(),
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

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeAck as RawMsgChannelUpgradeAck;

    use crate::core::ics04_channel::msgs::chan_upgrade_ack::test_util::get_dummy_raw_msg_chan_upgrade_ack;
    use crate::core::ics04_channel::msgs::chan_upgrade_ack::MsgChannelUpgradeAck;

    #[test]
    fn parse_channel_upgrade_try_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeAck,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_ack();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof channel".to_string(),
                raw: RawMsgChannelUpgradeAck {
                    proof_channel: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeAck::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "MsgChannelUpgradeAck::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_ack();
        let msg = MsgChannelUpgradeAck::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeAck::from(msg.clone());
        let msg_back = MsgChannelUpgradeAck::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
