use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeOpen as RawMsgChannelUpgradeOpen;
use ibc_proto::Protobuf;

use crate::core::ics04_channel::channel::State;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;
use crate::Height;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeOpen";

/// Message definition for the last step of the channel upgrade
/// handshake (the `ChanUpgradeOpen` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeOpen {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_channel_state: State,
    pub counterparty_upgrade_sequence: Sequence,
    /// The proof of the counterparty channel
    pub proof_channel: CommitmentProofBytes,
    /// The height at which the proofs were queried.
    pub proof_height: Height,
    pub signer: Signer,
}

impl MsgChannelUpgradeOpen {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        counterparty_channel_state: State,
        counterparty_upgrade_sequence: Sequence,
        proof_channel: CommitmentProofBytes,
        proof_height: Height,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            counterparty_channel_state,
            counterparty_upgrade_sequence,
            proof_channel,
            proof_height,
            signer,
        }
    }
}

impl Msg for MsgChannelUpgradeOpen {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeOpen;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeOpen> for MsgChannelUpgradeOpen {}

impl TryFrom<RawMsgChannelUpgradeOpen> for MsgChannelUpgradeOpen {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeOpen) -> Result<Self, Self::Error> {
        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeOpen {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            counterparty_channel_state: State::from_i32(raw_msg.counterparty_channel_state)?,
            counterparty_upgrade_sequence: raw_msg.counterparty_upgrade_sequence.into(),
            proof_channel: raw_msg
                .proof_channel
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_height,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgChannelUpgradeOpen> for RawMsgChannelUpgradeOpen {
    fn from(domain_msg: MsgChannelUpgradeOpen) -> Self {
        RawMsgChannelUpgradeOpen {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            counterparty_channel_state: domain_msg.counterparty_channel_state.as_i32(),
            counterparty_upgrade_sequence: domain_msg.counterparty_upgrade_sequence.into(),
            proof_channel: domain_msg.proof_channel.into(),
            proof_height: Some(domain_msg.proof_height.into()),
            signer: domain_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeOpen as RawMsgChannelUpgradeOpen;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeOpen`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_open() -> RawMsgChannelUpgradeOpen {
        RawMsgChannelUpgradeOpen {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            counterparty_channel_state: 6, // FlushComplete
            counterparty_upgrade_sequence: 1,
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

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeOpen as RawMsgChannelUpgradeOpen;

    use crate::core::ics04_channel::msgs::chan_upgrade_open::test_util::get_dummy_raw_msg_chan_upgrade_open;
    use crate::core::ics04_channel::msgs::chan_upgrade_open::MsgChannelUpgradeOpen;

    #[test]
    fn parse_channel_upgrade_try_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeOpen,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_open();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof channel".to_string(),
                raw: RawMsgChannelUpgradeOpen {
                    proof_channel: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeOpen::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "MsgChannelUpgradeOpen::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_open();
        let msg = MsgChannelUpgradeOpen::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeOpen::from(msg.clone());
        let msg_back = MsgChannelUpgradeOpen::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
