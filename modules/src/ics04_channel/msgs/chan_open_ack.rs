use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::channel::validate_version;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::{proofs::Proofs, tx_msg::Msg};

use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;
use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use std::convert::{TryFrom, TryInto};

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelOpenAck";

///
/// Message definition for the third step in the channel open handshake (`ChanOpenAck` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelOpenAck {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub counterparty_channel_id: ChannelId,
    pub counterparty_version: String,
    pub proofs: Proofs,
    pub signer: AccountId,
}

impl Msg for MsgChannelOpenAck {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl Protobuf<RawMsgChannelOpenAck> for MsgChannelOpenAck {}

impl TryFrom<RawMsgChannelOpenAck> for MsgChannelOpenAck {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgChannelOpenAck) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        let proofs = Proofs::new(
            raw_msg.proof_try.into(),
            None,
            None,
            raw_msg
                .proof_height
                .ok_or(Kind::MissingHeight)?
                .try_into()
                .map_err(|e| Kind::InvalidProof.context(e))?,
        )
        .map_err(|e| Kind::InvalidProof.context(e))?;

        Ok(MsgChannelOpenAck {
            port_id: raw_msg
                .port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: raw_msg
                .channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_channel_id: raw_msg
                .counterparty_channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_version: validate_version(raw_msg.counterparty_version)?,
            proofs,
            signer,
        })
    }
}

impl From<MsgChannelOpenAck> for RawMsgChannelOpenAck {
    fn from(domain_msg: MsgChannelOpenAck) -> Self {
        RawMsgChannelOpenAck {
            port_id: domain_msg.port_id.to_string(),
            channel_id: domain_msg.channel_id.to_string(),
            counterparty_channel_id: domain_msg.counterparty_channel_id.to_string(),
            counterparty_version: domain_msg.counterparty_version.to_string(),
            proof_try: domain_msg.proofs.object_proof().clone().into(),
            proof_height: Some(domain_msg.proofs.height().into()),
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;

    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};
    use ibc_proto::ibc::core::client::v1::Height;

    /// Returns a dummy `RawMsgChannelOpenAck`, for testing only!
    pub fn get_dummy_raw_msg_chan_open_ack(proof_height: u64) -> RawMsgChannelOpenAck {
        RawMsgChannelOpenAck {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            counterparty_channel_id: "cpartychannel".to_string(),
            counterparty_version: "v1".to_string(),
            proof_try: get_dummy_proof(),
            proof_height: Some(Height {
                revision_number: 1,
                revision_height: proof_height,
            }),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;

    use crate::ics04_channel::msgs::chan_open_ack::test_util::get_dummy_raw_msg_chan_open_ack;
    use crate::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
    use ibc_proto::ibc::core::client::v1::Height;
    use std::convert::TryFrom;

    #[test]
    fn parse_channel_open_ack_msg() {
        struct Test {
            name: String,
            raw: RawMsgChannelOpenAck,
            want_pass: bool,
        }

        let proof_height = 20;
        let default_raw_msg = get_dummy_raw_msg_chan_open_ack(proof_height);

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port identifier".to_string(),
                raw: RawMsgChannelOpenAck {
                    port_id: "p34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                raw: RawMsgChannelOpenAck {
                    port_id: "p".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                raw: RawMsgChannelOpenAck {
                    port_id: "abcdezdfDfsdfgfddsfsfdsdfdfvxcvzxcvsgdfsdfwefwvsdfdsfdasgagadgsadgsdffghijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                raw: RawMsgChannelOpenAck {
                    channel_id: "channelid34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                raw: RawMsgChannelOpenAck {
                    channel_id: "chshort".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                raw: RawMsgChannelOpenAck {
                    channel_id: "abcdefghsdfasdfasfdasfdwewefsdfasdfasdfasdfasdfasdfsfdijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "[Counterparty] Correct channel identifier".to_string(),
                raw: RawMsgChannelOpenAck {
                    counterparty_channel_id: "channelid34".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "[Counterparty] Bad channel, name too short".to_string(),
                raw: RawMsgChannelOpenAck {
                    counterparty_channel_id: "chshort".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "[Counterparty] Bad channel, name too long".to_string(),
                raw: RawMsgChannelOpenAck {
                    counterparty_channel_id: "abcdefghsdfasdfasfdasfdwewefsdfasdfasdfasdfasdfasdfsfdijklmnopqrstu".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty version (allowed)".to_string(),
                raw: RawMsgChannelOpenAck {
                    counterparty_version: " ".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Arbitrary counterparty version (allowed)".to_string(),
                raw: RawMsgChannelOpenAck {
                    counterparty_version: "v1.1.23-alpha".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                raw: RawMsgChannelOpenAck {
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
                raw: RawMsgChannelOpenAck {
                    proof_height: None,
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing proof try (object proof)".to_string(),
                raw: RawMsgChannelOpenAck {
                    proof_try: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
            .into_iter()
            .collect();

        for test in tests {
            let res_msg = MsgChannelOpenAck::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res_msg.is_ok(),
                "MsgChanOpenAck::try_from raw failed for test {}, \nraw msg {:?} with error {:?}",
                test.name,
                test.raw,
                res_msg.err(),
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_open_ack(100);
        let msg = MsgChannelOpenAck::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelOpenAck::from(msg.clone());
        let msg_back = MsgChannelOpenAck::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
