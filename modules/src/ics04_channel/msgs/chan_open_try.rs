use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::channel::{validate_version, ChannelEnd, Counterparty, Order};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;
use tendermint::account::Id as AccountId;
use tendermint_proto::DomainType;

use std::convert::{TryFrom, TryInto};
use std::str::FromStr;

/// Message type for the `MsgChannelOpenTry` message.
const TYPE_MSG_CHANNEL_OPEN_TRY: &str = "channel_open_try";

///
/// Message definition for the second step in the channel open handshake (`ChanOpenTry` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelOpenTry {
    port_id: PortId,
    channel_id: ChannelId, // Labeled `desired_channel_id` in raw types.
    counterparty_chosen_channel_id: Option<ChannelId>,
    channel: ChannelEnd,
    counterparty_version: String,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelOpenTry {
    #[allow(dead_code, clippy::too_many_arguments)]
    // TODO: Not used (yet). Also missing `counterparty_chosen_channel_id` value.
    fn new(
        port_id: String,
        channel_id: String,
        channel_version: String,
        order: i32,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        counterparty_version: String,
        proof_init: CommitmentProof,
        proofs_height: Height,
        signer: AccountId,
    ) -> Result<MsgChannelOpenTry, Error> {
        let connection_hops: Result<Vec<_>, _> = connection_hops
            .into_iter()
            .map(|s| ConnectionId::from_str(s.as_str()))
            .collect();

        let version =
            validate_version(channel_version).map_err(|e| Kind::InvalidVersion.context(e))?;

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_chosen_channel_id: None,
            channel: ChannelEnd::new(
                Order::from_i32(order)?,
                Counterparty::new(counterparty_port_id, counterparty_channel_id)
                    .map_err(|e| Kind::IdentifierError.context(e))?,
                connection_hops.map_err(|e| Kind::IdentifierError.context(e))?,
                version,
            ),
            counterparty_version: validate_version(counterparty_version)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(proof_init, None, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenTry {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_TRY.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.channel.validate_basic()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl DomainType<RawMsgChannelOpenTry> for MsgChannelOpenTry {}

impl TryFrom<RawMsgChannelOpenTry> for MsgChannelOpenTry {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgChannelOpenTry) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        let proofs = Proofs::new(
            raw_msg.proof_init.into(),
            None,
            None,
            raw_msg
                .proof_height
                .ok_or_else(|| Kind::MissingHeight)?
                .try_into()
                .map_err(|e| Kind::InvalidProof.context(e))?,
        )
        .map_err(|e| Kind::InvalidProof.context(e))?;

        let counterparty_chosen_channel_id = Some(raw_msg.counterparty_chosen_channel_id)
            .filter(|x| !x.is_empty())
            .map(|v| FromStr::from_str(v.as_str()))
            .transpose()
            .map_err(|e| Kind::IdentifierError.context(e))?;

        Ok(MsgChannelOpenTry {
            port_id: raw_msg
                .port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: raw_msg
                .desired_channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_chosen_channel_id,
            channel: raw_msg
                .channel
                .ok_or_else(|| Kind::MissingChannel)?
                .try_into()?,
            counterparty_version: validate_version(raw_msg.counterparty_version)?,
            proofs,
            signer,
        })
    }
}

impl From<MsgChannelOpenTry> for RawMsgChannelOpenTry {
    fn from(domain_msg: MsgChannelOpenTry) -> Self {
        RawMsgChannelOpenTry {
            port_id: domain_msg.port_id.to_string(),
            desired_channel_id: domain_msg.channel_id.to_string(),
            counterparty_chosen_channel_id: domain_msg
                .counterparty_chosen_channel_id
                .map_or_else(|| "".to_string(), |id| id.to_string()),
            channel: Some(domain_msg.channel.into()),
            counterparty_version: domain_msg.counterparty_version,
            proof_init: domain_msg.proofs.object_proof().clone().into(),
            proof_height: Some(domain_msg.proofs.height().into()),
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;

    use crate::ics04_channel::channel::test_util::get_dummy_raw_channel_end;
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};
    use ibc_proto::ibc::core::client::v1::Height;

    /// Returns a dummy `RawMsgChannelOpenTry`, for testing only!
    pub fn get_dummy_raw_msg_chan_open_try(proof_height: u64) -> RawMsgChannelOpenTry {
        RawMsgChannelOpenTry {
            port_id: "port".to_string(),
            desired_channel_id: "testchannel".to_string(),
            counterparty_chosen_channel_id: "".to_string(),
            channel: Some(get_dummy_raw_channel_end()),
            counterparty_version: "".to_string(),
            proof_init: get_dummy_proof(),
            proof_height: Some(Height {
                version_number: 1,
                version_height: proof_height,
            }),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ics04_channel::msgs::chan_open_try::test_util::get_dummy_raw_msg_chan_open_try;
    use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
    use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;
    use ibc_proto::ibc::core::client::v1::Height;
    use std::convert::TryFrom;

    #[test]
    fn channel_open_try_from_raw() {
        struct Test {
            name: String,
            raw: RawMsgChannelOpenTry,
            want_pass: bool,
        }

        let proof_height = 10;
        let default_raw_msg = get_dummy_raw_msg_chan_open_try(proof_height);

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port".to_string(),
                raw: RawMsgChannelOpenTry {
                    port_id: "p34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                raw: RawMsgChannelOpenTry {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                raw: RawMsgChannelOpenTry {
                    port_id: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                raw: RawMsgChannelOpenTry {
                    desired_channel_id: "channelid34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                raw: RawMsgChannelOpenTry {
                    desired_channel_id: "chshort".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                raw: RawMsgChannelOpenTry {
                    desired_channel_id: "abcdefghijkasdfasdfasdfasgdasdgasdfasdfadflmnoasdasdasdfasdfasdfasdfadadgadgadsfpqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty chosen channel id (valid choice)".to_string(),
                raw: RawMsgChannelOpenTry {
                    counterparty_chosen_channel_id: "".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "[Counterparty] Correct channel identifier".to_string(),
                raw: RawMsgChannelOpenTry {
                    counterparty_chosen_channel_id: "cpartyid34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "[Counterparty] Bad channel, name too short".to_string(),
                raw: RawMsgChannelOpenTry {
                    counterparty_chosen_channel_id: "cparty".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "[Counterparty] Bad channel, name too long".to_string(),
                raw: RawMsgChannelOpenTry {
                    counterparty_chosen_channel_id: "cpartydefghijkasdfasdfasdfasgdasdgasdfasdfadflmnoasdasdasdfasdfasdfasdfadadgadgadsfpqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty version (valid choice)".to_string(),
                raw: RawMsgChannelOpenTry {
                    counterparty_version: " ".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Arbitrary counterparty version (valid choice)".to_string(),
                raw: RawMsgChannelOpenTry {
                    counterparty_version: "anyversion".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                raw: RawMsgChannelOpenTry {
                    proof_height: Some(Height {
                        version_number: 0,
                        version_height: 0,
                    }),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing proof height".to_string(),
                raw: RawMsgChannelOpenTry {
                    proof_height: None,
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing proof init (object proof)".to_string(),
                raw: RawMsgChannelOpenTry {
                    proof_init: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
            .into_iter()
            .collect();

        for test in tests {
            let res_msg = MsgChannelOpenTry::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res_msg.is_ok(),
                "MsgChanOpenTry::try_from failed for test {}, \nraw msg {:?} with error {:?}",
                test.name,
                test.raw,
                res_msg.err(),
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_open_try(10);
        let msg = MsgChannelOpenTry::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelOpenTry::from(msg.clone());
        let msg_back = MsgChannelOpenTry::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
