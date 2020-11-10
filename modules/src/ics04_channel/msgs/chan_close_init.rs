use crate::ics04_channel::error::{Error, Kind};
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::tx_msg::Msg;

use tendermint::account::Id as AccountId;

/// Message type for the `MsgChannelCloseInit` message.
const TYPE_MSG_CHANNEL_CLOSE_INIT: &str = "channel_close_init";

///
/// Message definition for the first step in the channel close handshake (`ChanCloseInit` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelCloseInit {
    port_id: PortId,
    channel_id: ChannelId,
    signer: AccountId,
}

impl MsgChannelCloseInit {
    pub fn new(
        port_id: String,
        channel_id: String,
        signer: AccountId,
    ) -> Result<MsgChannelCloseInit, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelCloseInit {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_CLOSE_INIT.to_string()
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
    use crate::ics04_channel::msgs::chan_close_init::MsgChannelCloseInit;
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_close_init_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct CloseInitParams {
            port_id: String,
            channel_id: String,
        }

        let default_params = CloseInitParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
        };

        struct Test {
            name: String,
            params: CloseInitParams,
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
                params: CloseInitParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: CloseInitParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: CloseInitParams {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: CloseInitParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: CloseInitParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: CloseInitParams {
                    channel_id: "abcdeasdfasdfasdfasdfasdfasdfasdfasdfdgasdfasdfasdfghijklmnopqrstu".to_string(),
                    ..default_params
                },
                want_pass: false,
            },
        ]
            .into_iter()
            .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelCloseInit::new(p.port_id, p.channel_id, acc);

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanCloseInit::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }
}
