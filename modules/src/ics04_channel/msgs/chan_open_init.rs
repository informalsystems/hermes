#![allow(clippy::too_many_arguments)]

use crate::ics04_channel::channel::{ChannelEnd, Counterparty, Order};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::tx_msg::Msg;

use tendermint::account::Id as AccountId;

use std::str::FromStr;

/// Message type for the `MsgChannelOpenInit` message.
const TYPE_MSG_CHANNEL_OPEN_INIT: &str = "channel_open_init";

///
/// Message definition for the first step in the channel open handshake (`ChanOpenInit` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelOpenInit {
    port_id: PortId,
    channel_id: ChannelId,
    channel: ChannelEnd,
    signer: AccountId,
}

impl MsgChannelOpenInit {
    pub fn new(
        port_id: String,
        channel_id: String,
        version: String,
        order: i32,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        signer: AccountId,
    ) -> Result<MsgChannelOpenInit, Error> {
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
            channel: ChannelEnd::new(
                Order::from_i32(order)?,
                Counterparty::new(counterparty_port_id, counterparty_channel_id)
                    .map_err(|e| Kind::IdentifierError.context(e))?,
                connection_hops.map_err(|e| Kind::IdentifierError.context(e))?,
                version,
            ),
            signer,
        })
    }
}

impl Msg for MsgChannelOpenInit {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_INIT.to_string()
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
    use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_open_init_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenInitParams {
            port_id: String,
            channel_id: String,
            version: String,
            order: i32,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
        }

        let default_params = OpenInitParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            version: "1.0".to_string(),
            order: Order::from_str("ORDERED").unwrap() as i32,
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
                name: "Correct port identifier".to_string(),
                params: OpenInitParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Incorrect port identifier, slash (separator) prohibited".to_string(),
                params: OpenInitParams {
                    port_id: "p34/".to_string(),
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
                    order: 99,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection hops (conn id too short, must be 10 chars)".to_string(),
                params: OpenInitParams {
                    connection_hops: vec!["conn124".to_string()].into_iter().collect(),
                    ..default_params
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

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenInit::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }
}
