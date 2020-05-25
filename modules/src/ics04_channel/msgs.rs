#![allow(clippy::too_many_arguments)]
use super::channel::{Channel, Endpoint};
use super::exported::*;
use crate::ics04_channel::error::Kind;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use serde_derive::{Deserialize, Serialize};
use std::str::FromStr;
use tendermint::account::Id as AccountId;

pub const TYPE_MSG_CHANNEL_OPEN_INIT: &str = "channel_open_init";

// FIXME - this should be common for all messages not just channel, client also defines it.
pub trait Msg {
    type ValidationError: std::error::Error;

    fn route(&self) -> String;

    fn get_type(&self) -> String;

    fn validate_basic(&self) -> Result<(), Self::ValidationError>;

    fn get_sign_bytes(&self) -> Vec<u8>;

    fn get_signers(&self) -> Vec<AccountId>;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelOpenInit {
    port_id: PortId,
    channel_id: ChannelId,
    channel: Channel,
    signer: AccountId,
}

impl MsgChannelOpenInit {
    pub fn new(
        port_id: String,
        channel_id: String,
        version: String,
        order: String,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        signer: AccountId,
    ) -> Result<MsgChannelOpenInit, crate::ics04_channel::error::Error> {
        let connection_hops: Result<Vec<_>, _> = connection_hops
            .into_iter()
            .map(|s| ConnectionId::from_str(s.as_str()))
            .collect();

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel: Channel::new(
                order.parse()?,
                Endpoint::new(counterparty_port_id, counterparty_channel_id)
                    .map_err(|e| Kind::IdentifierError.context(e))?,
                connection_hops.map_err(|e| Kind::IdentifierError.context(e))?,
                version,
            ),
            signer,
        })
    }
}

impl Msg for MsgChannelOpenInit {
    type ValidationError = crate::ics04_channel::error::Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_INIT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.channel.validate_basic()
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_open_init_msg() {
        use super::MsgChannelOpenInit;
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenInitParams {
            port_id: String,
            channel_id: String,
            version: String,
            order: String,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
        }

        let default_params = OpenInitParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            version: "1.0".to_string(),
            order: "ORDERED".to_string(),
            connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
            counterparty_port_id: "destport".to_string(),
            counterparty_channel_id: "testdestchannel".to_string(),
        };

        struct Test {
            name: String,
            params: OpenInitParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad port, non-alpha".to_string(),
                params: OpenInitParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenInitParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad version".to_string(),
                params: OpenInitParams {
                    version: " . ".to_string(),
                    ..default_params.clone()
                },
                want_pass: true, // verified in validate_basic()
            },
            Test {
                name: "Bad order".to_string(),
                params: OpenInitParams {
                    order: "MYORER".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection hops".to_string(),
                params: OpenInitParams {
                    connection_hops: vec!["conn124".to_string()].into_iter().collect(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenInit::new(
                p.port_id,
                p.channel_id,
                p.version,
                p.order,
                p.connection_hops,
                p.counterparty_port_id,
                p.counterparty_channel_id,
                acc,
            );

            match msg {
                Ok(_res) => {
                    assert!(
                        test.want_pass,
                        "MsgChanOpenInit::new should have failed for test {}, \nmsg {:?}",
                        test.name,
                        test.params.clone()
                    );
                }
                Err(err) => {
                    assert!(
                        !test.want_pass,
                        "MsgChanOpenInit::new failed for test {}, \nmsg {:?} with err {:?}",
                        test.name,
                        test.params.clone(),
                        err
                    );
                }
            }
        }
    }
}
