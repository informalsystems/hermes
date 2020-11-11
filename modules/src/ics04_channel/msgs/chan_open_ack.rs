use crate::ics03_connection::connection::validate_version;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use tendermint::account::Id as AccountId;

/// Message type for the `MsgChannelOpenAck` message.
const TYPE_MSG_CHANNEL_OPEN_ACK: &str = "channel_open_ack";

///
/// Message definition for the third step in the channel open handshake (`ChanOpenAck` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelOpenAck {
    port_id: PortId,
    channel_id: ChannelId,
    counterparty_version: String,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelOpenAck {
    pub fn new(
        port_id: String,
        channel_id: String,
        counterparty_version: String,
        proof_try: CommitmentProof,
        proofs_height: Height,
        signer: AccountId,
    ) -> Result<MsgChannelOpenAck, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_version: validate_version(counterparty_version)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(proof_try, None, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenAck {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_ACK.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

#[cfg(test)]
mod tests {
    use crate::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
    use crate::ics23_commitment::commitment::CommitmentProof;
    use crate::test_utils::get_dummy_proof;
    use crate::Height;
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_open_ack_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenAckParams {
            port_id: String,
            channel_id: String,
            counterparty_version: String,
            proof_try: CommitmentProof,
            proof_height: Height,
        }

        let default_params = OpenAckParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            counterparty_version: "1.0".to_string(),
            proof_try: get_dummy_proof().into(),
            proof_height: Height {
                version_number: 0,
                version_height: 10,
            },
        };

        struct Test {
            name: String,
            params: OpenAckParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port identifier".to_string(),
                params: OpenAckParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: OpenAckParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: OpenAckParams {
                    port_id: "abcdezdfDfsdfgfddsfsfdsdfdfvxcvzxcvsgdfsdfwefwvsdfdsfdasgagadgsadgsdffghijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: OpenAckParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenAckParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: OpenAckParams {
                    channel_id: "abcdefghsdfasdfasfdasfdwewefsdfasdfasdfasdfasdfasdfsfdijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty version".to_string(),
                params: OpenAckParams {
                    counterparty_version: " ".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                params: OpenAckParams {
                    proof_height: Height {
                        version_number: 0,
                        version_height: 0,
                    },
                    ..default_params
                },
                want_pass: false,
            },
        ]
            .into_iter()
            .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenAck::new(
                p.port_id,
                p.channel_id,
                p.counterparty_version,
                p.proof_try,
                p.proof_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenAck::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }
}
