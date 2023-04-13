use crate::timestamp::Timestamp;
use crate::{prelude::*, Height};

use ibc_proto::protobuf::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
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
    pub counterparty_channel: Option<ChannelEnd>,
    pub counterparty_sequence: u64,
    pub proposed_upgrade_channel: Option<ChannelEnd>,
    pub timeout_height: Option<Height>,
    pub timeout_timestamp: Timestamp,
    pub proof_channel: CommitmentProofBytes,
    pub proof_upgrade_timeout: CommitmentProofBytes,
    pub proof_upgrade_sequence: CommitmentProofBytes,
    pub proof_height: Option<Height>,
}

impl MsgChannelUpgradeTry {
    pub fn new(
        port_id: PortId, 
        channel_id: ChannelId, 
        signer: Signer,
        counterparty_channel: Option<ChannelEnd>,
        counterparty_sequence: u64,
        proposed_upgrade_channel: Option<ChannelEnd>,
        timeout_height: Option<Height>,
        timeout_timestamp: Timestamp,
        proof_channel: CommitmentProofBytes,
        proof_upgrade_timeout: CommitmentProofBytes,
        proof_upgrade_sequence: CommitmentProofBytes,
        proof_height: Option<Height>,
    ) -> Self {
        Self {
            port_id,
            channel_id,
            signer,
            counterparty_channel,
            counterparty_sequence,
            proposed_upgrade_channel,
            timeout_height,
            timeout_timestamp,
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

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.port_id.validate_basic()?;
        self.channel_id.validate_basic()?;
        self.signer.validate_basic()?;

        self.proposed_upgrade_channel
            .as_ref()
            .ok_or_else(|| Error::missing_proposed_channel())?
            .validate_basic()?;
        self.timeout_height
            .as_ref()
            .ok_or_else(|| Error::missing_timeout_height())?
            .validate_basic()?;

        if self.counterparty_sequence == 0 {
            return Err(Error::invalid_counterparty_sequence(self.counterparty_sequence));
        }

        if self.timeout_timestamp.is_zero() {
            return Err(Error::invalid_timeout());
        }

        if self.proof_channel.is_empty() {
            return Err(Error::empty_proof());
        }

        if self.proof_upgrade_timeout.is_empty() {
            return Err(Error::empty_proof());
        }

        if self.proof_upgrade_sequence.is_empty() {
            return Err(Error::empty_proof());
        }

        if self.proof_height.is_none() {
            return Err(Error::empty_proof_height());
        }

        Ok(())
    }
}

impl Protobuf<RawMsgChannelUpgradeTry> for MsgChannelUpgradeTry {}

impl TryFrom<RawMsgChannelUpgradeTry> for MsgChannelUpgradeTry {
    type Error = Error;

    fn try_from(raw_msg: RawMsgChannelUpgradeTry) -> Result<Self, Self::Error> {
        let counterparty_channel: ChannelEnd = raw_msg
            .counterparty_channel
            .ok_or_else(|| Error::missing_counterparty_channel())?
            .try_into()?;
        let proposed_upgrade_channel: ChannelEnd = raw_msg
            .proposed_upgrade_channel
            .ok_or_else(|| Error::missing_proposed_channel())?
            .try_into()?;

        let msg = MsgChannelUpgradeTry {
            port_id: raw_msg.port_id.parse().map_err(Error::identifier)?,
            channel_id: raw_msg.channel_id.parse().map_err(Error::identifier)?,
            signer: raw_msg.signer.parse().map_err(Error::signer)?,
            counterparty_channel: Some(counterparty_channel),
            proposed_upgrade_channel: Some(proposed_upgrade_channel),
            counterparty_sequence: raw_msg.counterparty_sequence,
            timeout_height: raw_msg.timeout_height.map(Height::from),
            timeout_timestamp: raw_msg.timeout_timestamp.into(),
            proof_channel: raw_msg.proof_channel.into(),
            proof_upgrade_timeout: raw_msg.proof_upgrade_timeout.into(),
            proof_upgrade_sequence: raw_msg.proof_upgrade_sequence.into(),
            proof_height: raw_msg.proof_height.map(Height::from),
        };

        msg.validate_basic()?;

        Ok(msg)
    }
}

impl From<MsgChannelUpgradeTry> for RawMsgChannelUpgradeTry {
    fn from(domain_msg: MsgChannelUpgradeTry) -> Self {
        RawMsgChannelUpgradeTry {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            signer: domain_msg.signer.to_string(),
            counterparty_channel: domain_msg.counterparty_channel.map(Into::into),
            counterparty_sequence: domain_msg.counterparty_sequence,
            proposed_upgrade_channel: domain_msg.proposed_upgrade_channel.map(Into::into),
            timeout_height: domain_msg.timeout_height.map(Into::into),
            timeout_timestamp: domain_msg.timeout_timestamp.into(),
            proof_channel: domain_msg.proof_channel.into(),
            proof_upgrade_timeout: domain_msg.proof_upgrade_timeout.into(),
            proof_upgrade_sequence: domain_msg.proof_upgrade_sequence.into(),
            proof_height: domain_msg.proof_height.map(Into::into),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::prelude::*;
    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

    use crate::core::ics04_channel::channel::test_util::get_dummy_raw_channel_end;
    use crate::core::ics24_host::identifier::{ChannelId, PortId};
    use crate::test_utils::get_dummy_bech32_account;

    /// Returns a dummy `RawMsgChannelUpgradeTry`, for testing only!
    pub fn get_dummy_raw_chan_upgrade_try() -> RawMsgChannelOpenTry {
        RawMsgChannelUpgradeTry {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
            signer: get_dummy_bech32_account(),
            counterparty_channel: Some(get_dummy_raw_channel_end()),
            counterparty_sequence: 1,
            proposed_upgrade_channel: Some(get_dummy_raw_channel_end()),
            timeout_height: Some(get_dummy_raw_height()),
            timeout_timestamp: Timestamp::now().into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use test_log::test;

    use ibc_proto::ibc::core::channel::v1::MsgChannelUpgradeTry as RawMsgChannelUpgradeTry;

    use crate::core::ics04_channel::msgs::chan_upgrade_init::test_util::get_dummy_raw_msg_chan_upgrade_init;
    use crate::core::ics04_channel::msgs::chan_upgrade_init::MsgChannelUpgradeTry;

    #[test]
    fn parse_channel_upgrade_init_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelUpgradeTry,
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
        let raw = get_dummy_raw_msg_chan_upgrade_init();
        let msg = MsgChannelUpgradeTry::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelUpgradeTry::from(msg.clone());
        let msg_back = MsgChannelUpgradeTry::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}