#![allow(clippy::too_many_arguments)]

use crate::ics03_connection::connection::validate_version;
use crate::ics04_channel::channel::{ChannelEnd, Counterparty, Order};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use tendermint::account::Id as AccountId;

use std::str::FromStr;

/// Message type for the `MsgChannelOpenTry` message.
const TYPE_MSG_CHANNEL_OPEN_TRY: &str = "channel_open_try";

///
/// Message definition for the second step in the channel open handshake (`ChanOpenTry` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelOpenTry {
    port_id: PortId,
    channel_id: ChannelId,
    channel: ChannelEnd,
    counterparty_version: String,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelOpenTry {
    pub fn new(
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

#[cfg(test)]
mod tests {
    use crate::ics04_channel::channel::Order;
    use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
    use crate::ics23_commitment::commitment::CommitmentProof;
    use crate::test_utils::get_dummy_proof;
    use crate::Height;
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_open_try_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenTryParams {
            port_id: String,
            channel_id: String,
            channel_version: String,
            order: i32,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
            counterparty_version: String,
            proof_init: CommitmentProof,
            proof_height: Height,
        }

        let default_params = OpenTryParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            channel_version: "1.0".to_string(),
            order: Order::from_str("ORDERED").unwrap() as i32,
            connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
            counterparty_port_id: "destport".to_string(),
            counterparty_channel_id: "testdestchannel".to_string(),
            counterparty_version: "1.0".to_string(),
            proof_init: get_dummy_proof().into(),
            proof_height: Height {
                version_number: 0,
                version_height: 10,
            },
        };

        struct Test {
            name: String,
            params: OpenTryParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port".to_string(),
                params: OpenTryParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: OpenTryParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: OpenTryParams {
                    port_id: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: OpenTryParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenTryParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: OpenTryParams {
                    channel_id: "abcdefghijkasdfasdfasdfasgdasdgasdfasdfadflmnoasdasdasdfasdfasdfasdfadadgadgadsfpqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty version".to_string(),
                params: OpenTryParams {
                    counterparty_version: " ".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                params: OpenTryParams {
                    proof_height: Height {
                        version_number: 0,
                        version_height: 0,
                    },
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad order".to_string(),
                params: OpenTryParams {
                    order: 99,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct connection hops (connection id)".to_string(),
                params: OpenTryParams {
                    connection_hops: vec!["connection124".to_string()].into_iter().collect(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad connection hops, connection id too long".to_string(),
                params: OpenTryParams {
                    connection_hops: vec!["abcdefghadvvxvczxcvzxvxvzxvcsddsfsdsdfasdfasfasdasdgasdfasdfasdfadsfasdfijklmnopqrstu".to_string()]
                        .into_iter()
                        .collect(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection hops, connection id too short".to_string(),
                params: OpenTryParams {
                    connection_hops: vec!["connid".to_string()].into_iter().collect(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            // Currently failing because we don't validate connection hops
            // Test {
            //     name: "Bad connection hops, more than 1".to_string(),
            //     params: OpenTryParams {
            //         connection_hops: vec!["connectionhop".to_string(), "connectionhopnext".to_string()].into_iter().collect(),
            //         ..default_params.clone()
            //     },
            //     want_pass: false,
            // },
            Test {
                name: "Empty channel version".to_string(),
                params: OpenTryParams {
                    channel_version: " ".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad counterparty port, name too long".to_string(),
                params: OpenTryParams {
                    counterparty_port_id: "abcdefgaszdsfgasdasdvsdfasdfasdfdfasdfasdfadsgasdfasdfasdfasdfasdfasdfhijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct counterparty channel identifier".to_string(),
                params: OpenTryParams {
                    counterparty_channel_id: "channelid34".to_string(),
                    ..default_params
                },
                want_pass: true,
            },
        ]
            .into_iter()
            .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenTry::new(
                p.port_id,
                p.channel_id,
                p.channel_version,
                p.order,
                p.connection_hops,
                p.counterparty_port_id,
                p.counterparty_channel_id,
                p.counterparty_version,
                p.proof_init,
                p.proof_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenTry::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }
}
