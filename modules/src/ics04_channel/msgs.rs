use super::channel::{Channel, Endpoint};
use super::exported::*;
use crate::ics24_host::identifier::{ChannelId, PortId};
use serde_derive::{Deserialize, Serialize};
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
    /*
        pub fn new1(
            port_id: String,
            channel_id: String,
            version: String,
            order: String,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
            signer: AccountId,
        ) -> Result<MsgChannelOpenInit, crate::ics04_channel::error::Error>
        {
            let counterparty = Endpoint::new(counterparty_port_id, counterparty_channel_id);
            Ok(Self {
                port_id: port_id.parse()?,
                channel_id: channel_id.parse()?,
                channel: Channel::new(order.parse()?, counterparty, connection_hops, version),
                signer,
            })
        }
    */
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
        let counterparty = Endpoint::new(counterparty_port_id, counterparty_channel_id);
        let order = order.parse()?;
        Ok(Self {
            port_id: port_id.parse().unwrap(),
            channel_id: channel_id.parse().unwrap(),
            channel: Channel::new(order, counterparty, connection_hops, version),
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
        vec![self.signer.clone()]
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

        let msgs: Vec<OpenInitParams> = vec![
            // Good parameters
            OpenInitParams {
                port_id: "port".to_string(),
                channel_id: "testchannel".to_string(),
                version: "1.0".to_string(),
                order: "ORDERED".to_string(),
                connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
                counterparty_port_id: "destport".to_string(),
                counterparty_channel_id: "testdestchannel".to_string(),
            },
            // Bad order
            OpenInitParams {
                port_id: "test".to_string(),
                channel_id: "testchannel".to_string(),
                version: "1.0".to_string(),
                order: "MYORER".to_string(),
                connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
                counterparty_port_id: "destport".to_string(),
                counterparty_channel_id: "testdestchannel".to_string(),
            },
            // Bad version
            OpenInitParams {
                port_id: "test".to_string(),
                channel_id: "testchannel".to_string(),
                version: " . ".to_string(),
                order: "MYORER".to_string(),
                connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
                counterparty_port_id: "destport".to_string(),
                counterparty_channel_id: "testdestchannel".to_string(),
            },
        ]
        .into_iter()
        .collect();

        struct Test {
            params: usize,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                params: 0,
                want_pass: true,
            },
            Test {
                params: 1,
                want_pass: true,
            },
            Test {
                params: 2,
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = msgs[test.params].clone();

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
                        "MsgConnOpenInit::new should have failed for test {}, \nmsg {:?}",
                        test.params, msgs[test.params]
                    );
                }
                Err(_err) => {
                    assert!(
                        !test.want_pass,
                        "MsgConnOpenInit::new failed for test {}, \nmsg {:?}",
                        test.params, msgs[test.params]
                    );
                }
            }
        }
    }
}
