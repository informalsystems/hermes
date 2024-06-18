use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeConfirm as RawMsgChannelUpgradeConfirm;
use ibc_proto::Protobuf;

use crate::core::ics04_channel::channel::State;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::upgrade::Upgrade;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;
use crate::Height;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeConfirm";

/// Message definition for the third step of the channel upgrade
/// handshake (the `ChanUpgradeConfirm` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeConfirm {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_channel_state: State,
    pub counterparty_upgrade: Upgrade,
    /// The proof of the counterparty channel
    pub proof_channel: CommitmentProofBytes,
    /// The proof of the counterparty upgrade
    pub proof_upgrade: CommitmentProofBytes,
    /// The height at which the proofs were queried.
    pub proof_height: Height,
    pub signer: Signer,
}

impl MsgChannelUpgradeConfirm {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        counterparty_channel_state: State,
        counterparty_upgrade: Upgrade,
        proof_channel: CommitmentProofBytes,
        proof_upgrade: CommitmentProofBytes,
        proof_height: Height,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            counterparty_channel_state,
            counterparty_upgrade,
            proof_channel,
            proof_upgrade,
            proof_height,
            signer,
        }
    }
}

impl Msg for MsgChannelUpgradeConfirm {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeConfirm;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeConfirm> for MsgChannelUpgradeConfirm {}

impl TryFrom<RawMsgChannelUpgradeConfirm> for MsgChannelUpgradeConfirm {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeConfirm) -> Result<Self, Self::Error> {
        let counterparty_upgrade = raw_msg
            .counterparty_upgrade
            .ok_or(Error::missing_upgrade())?
            .try_into()?;

        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeConfirm {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            counterparty_channel_state: State::from_i32(raw_msg.counterparty_channel_state)?,
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

impl From<MsgChannelUpgradeConfirm> for RawMsgChannelUpgradeConfirm {
    fn from(domain_msg: MsgChannelUpgradeConfirm) -> Self {
        RawMsgChannelUpgradeConfirm {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            counterparty_channel_state: domain_msg.counterparty_channel_state.as_i32(),
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
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeConfirm as RawMsgChannelUpgradeConfirm;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics04_channel::upgrade::test_util::get_dummy_upgrade;
    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeConfirm`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_confirm() -> RawMsgChannelUpgradeConfirm {
        RawMsgChannelUpgradeConfirm {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            counterparty_channel_state: 6, // FlushComplete
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

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeConfirm as RawMsgChannelUpgradeConfirm;

    use crate::core::ics04_channel::msgs::chan_upgrade_confirm::test_util::get_dummy_raw_msg_chan_upgrade_confirm;
    use crate::core::ics04_channel::msgs::chan_upgrade_confirm::MsgChannelUpgradeConfirm;

    #[test]
    fn parse_channel_upgrade_try_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeConfirm,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_confirm();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof channel".to_string(),
                raw: RawMsgChannelUpgradeConfirm {
                    proof_channel: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeConfirm::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "MsgChannelUpgradeConfirm::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_confirm();
        let msg = MsgChannelUpgradeConfirm::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeConfirm::from(msg.clone());
        let msg_back = MsgChannelUpgradeConfirm::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
