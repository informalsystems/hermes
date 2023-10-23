use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics04_channel::upgrade_fields::UpgradeFields;
use crate::Height;

use ibc_proto::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

use crate::core::ics04_channel::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeTry";

/// Message definition for the second step of the channel upgrade
/// handshake (the `ChanUpgradeTry` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeTry {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub proposed_upgrade_connection_hops: Vec<ConnectionId>,
    pub counterparty_upgrade_fields: UpgradeFields,
    pub counterparty_upgrade_sequence: Sequence,
    /// The proof of the counterparty channel
    pub proof_channel: CommitmentProofBytes,
    /// The proof of the counterparty upgrade
    pub proof_upgrade: CommitmentProofBytes,
    /// The height at which the proofs were queried.
    pub proof_height: Height,
    pub signer: Signer,
}

impl MsgChannelUpgradeTry {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        proposed_upgrade_connection_hops: Vec<ConnectionId>,
        counterparty_upgrade_fields: UpgradeFields,
        counterparty_upgrade_sequence: Sequence,
        proof_channel: CommitmentProofBytes,
        proof_upgrade: CommitmentProofBytes,
        proof_height: Height,
        signer: Signer,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            proposed_upgrade_connection_hops,
            counterparty_upgrade_fields,
            counterparty_upgrade_sequence,
            proof_channel,
            proof_upgrade,
            proof_height,
            signer,
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
        let proposed_upgrade_connection_hops: Result<Vec<ConnectionId>, Error> = raw_msg
            .proposed_upgrade_connection_hops
            .iter()
            .map(|hop| hop.parse().map_err(Error::identifier))
            .collect();
        let counterparty_upgrade_fields = raw_msg
            .counterparty_upgrade_fields
            .ok_or(Error::missing_upgrade_fields())?
            .try_into()?;
        let counterparty_upgrade_sequence = raw_msg.counterparty_upgrade_sequence.into();

        let proof_height = raw_msg
            .proof_height
            .ok_or_else(Error::missing_proof_height)?
            .try_into()
            .map_err(|_| Error::invalid_proof_height())?;

        Ok(MsgChannelUpgradeTry {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            proposed_upgrade_connection_hops: proposed_upgrade_connection_hops?,
            counterparty_upgrade_fields,
            counterparty_upgrade_sequence,
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

impl From<MsgChannelUpgradeTry> for RawMsgChannelUpgradeTry {
    fn from(domain_msg: MsgChannelUpgradeTry) -> Self {
        let proposed_upgrade_connection_hops = domain_msg
            .proposed_upgrade_connection_hops
            .into_iter()
            .map(|hop| hop.to_string())
            .collect();

        RawMsgChannelUpgradeTry {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            proposed_upgrade_connection_hops,
            counterparty_upgrade_fields: Some(domain_msg.counterparty_upgrade_fields.into()),
            counterparty_upgrade_sequence: domain_msg.counterparty_upgrade_sequence.into(),
            proof_upgrade: domain_msg.proof_upgrade.into(),
            proof_channel: domain_msg.proof_channel.into(),
            proof_height: Some(domain_msg.proof_height.into()),
            signer: domain_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::core::ics04_channel::upgrade_fields::test_util::get_dummy_upgrade_fields;
    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgChannelUpgradeTry`, for testing only!
    pub fn get_dummy_raw_msg_chan_upgrade_try() -> RawMsgChannelUpgradeTry {
        RawMsgChannelUpgradeTry {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            proposed_upgrade_connection_hops: vec![],
            counterparty_upgrade_fields: Some(get_dummy_upgrade_fields()),
            counterparty_upgrade_sequence: 1,
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

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

    use crate::core::ics04_channel::msgs::chan_upgrade_try::test_util::get_dummy_raw_msg_chan_upgrade_try;
    use crate::core::ics04_channel::msgs::chan_upgrade_try::MsgChannelUpgradeTry;

    #[test]
    fn parse_channel_upgrade_try_msg() {
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
                    ..default_raw_msg
                },
                want_pass: false,
            },
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
