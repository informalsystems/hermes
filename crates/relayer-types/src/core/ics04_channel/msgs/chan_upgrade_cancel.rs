use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeCancel as RawMsgChannelUpgradeCancel;
use ibc_proto::Protobuf;

use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::upgrade::ErrorReceipt;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;
use crate::Height;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeCancel";

/// Message definition the `ChanUpgradeCancel` datagram.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeCancel {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub error_receipt: ErrorReceipt,
    /// The proof of the counterparty error receipt
    pub proof_error_receipt: CommitmentProofBytes,
    /// The height at which the proofs were queried.
    pub proof_height: Height,
    pub signer: Signer,
}

impl MsgChannelUpgradeCancel {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        error_receipt: ErrorReceipt,
        proof_error_receipt: CommitmentProofBytes,
        proof_height: Height,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            error_receipt,
            proof_error_receipt,
            proof_height,
            signer,
        }
    }
}

impl Msg for MsgChannelUpgradeCancel {
    type ValidationError = Error;
    type Raw = RawMsgChannelUpgradeCancel;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgChannelUpgradeCancel> for MsgChannelUpgradeCancel {}

impl TryFrom<RawMsgChannelUpgradeCancel> for MsgChannelUpgradeCancel {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeCancel) -> Result<Self, Self::Error> {
        let raw_error_receipt = raw_msg
            .error_receipt
            .ok_or(Error::missing_upgrade_error_receipt())?;
        let error_receipt = ErrorReceipt::try_from(raw_error_receipt)?;

        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeCancel {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            error_receipt,
            proof_error_receipt: raw_msg
                .proof_error_receipt
                .try_into()
                .map_err(Error::invalid_proof)?,
            proof_height,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgChannelUpgradeCancel> for RawMsgChannelUpgradeCancel {
    fn from(domain_msg: MsgChannelUpgradeCancel) -> Self {
        RawMsgChannelUpgradeCancel {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            error_receipt: Some(domain_msg.error_receipt.into()),
            proof_error_receipt: domain_msg.proof_error_receipt.into(),
            proof_height: Some(domain_msg.proof_height.into()),
            signer: domain_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::ErrorReceipt as RawErrorReceipt;
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeCancel as RawMsgChannelUpgradeCancel;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeCnacel`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_cancel() -> RawMsgChannelUpgradeCancel {
        RawMsgChannelUpgradeCancel {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            error_receipt: Some(RawErrorReceipt {
                sequence: 1,
                message: "error message".to_string(),
            }),
            proof_error_receipt: get_dummy_proof(),
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

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeCancel as RawMsgChannelUpgradeCancel;

    use crate::core::ics04_channel::msgs::chan_upgrade_cancel::test_util::get_dummy_raw_msg_chan_upgrade_cancel;
    use crate::core::ics04_channel::msgs::chan_upgrade_cancel::MsgChannelUpgradeCancel;

    #[test]
    fn parse_channel_upgrade_try_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeCancel,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_upgrade_cancel();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port ID".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    port_id: "p36".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Port too short".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Port too long".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstuabcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel ID".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    channel_id: "channel-2".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Channel name too short".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    channel_id: "c".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Channel name too long".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    channel_id: "channel-128391283791827398127398791283912837918273981273987912839".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof channel".to_string(),
                raw: RawMsgChannelUpgradeCancel {
                    proof_error_receipt: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = MsgChannelUpgradeCancel::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "RawMsgChannelUpgradeCancel::try_from failed for test {}, \nraw msg {:?} with err {:?}",
                test.name,
                test.raw,
                res.err()
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_upgrade_cancel();
        let msg = MsgChannelUpgradeCancel::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeCancel::from(msg.clone());
        let msg_back = MsgChannelUpgradeCancel::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
