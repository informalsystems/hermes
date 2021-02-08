use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics24_host::identifier::PortId;
use crate::tx_msg::Msg;

use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;
use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use std::convert::{TryFrom, TryInto};

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelOpenInit";

///
/// Message definition for the first step in the channel open handshake (`ChanOpenInit` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgChannelOpenInit {
    pub port_id: PortId,
    pub channel: ChannelEnd,
    pub signer: AccountId,
}

impl MsgChannelOpenInit {
    /// Getter: borrow the `port_id` from this message.
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    /// Getter: borrow the `channelEnd` from this message.
    pub fn channel(&self) -> &ChannelEnd {
        &self.channel
    }
}

impl Msg for MsgChannelOpenInit {
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

impl Protobuf<RawMsgChannelOpenInit> for MsgChannelOpenInit {}

impl TryFrom<RawMsgChannelOpenInit> for MsgChannelOpenInit {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgChannelOpenInit) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        Ok(MsgChannelOpenInit {
            port_id: raw_msg
                .port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel: raw_msg.channel.ok_or(Kind::MissingChannel)?.try_into()?,
            signer,
        })
    }
}

impl From<MsgChannelOpenInit> for RawMsgChannelOpenInit {
    fn from(domain_msg: MsgChannelOpenInit) -> Self {
        RawMsgChannelOpenInit {
            port_id: domain_msg.port_id.to_string(),
            channel: Some(domain_msg.channel.into()),
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;

    use crate::ics04_channel::channel::test_util::get_dummy_raw_channel_end_with_missing_connection;
    use crate::ics04_channel::channel::test_util::{
        get_dummy_raw_channel_end, get_dummy_raw_channel_end_ics26,
    };
    use crate::test_utils::get_dummy_bech32_account;
    //use crate::ics04_channel::channel::State;

    /// Returns a dummy `RawMsgChannelOpenInit`, for testing only!
    pub fn get_dummy_raw_msg_chan_open_init() -> RawMsgChannelOpenInit {
        RawMsgChannelOpenInit {
            port_id: "port".to_string(),
            channel: Some(get_dummy_raw_channel_end()),
            signer: get_dummy_bech32_account(),
        }
    }

    /// Returns a dummy `RawMsgChannelOpenInit`, for testing only!
    pub fn get_dummy_raw_msg_chan_open_init_ics26() -> RawMsgChannelOpenInit {
        RawMsgChannelOpenInit {
            port_id: "port".to_string(),
            channel: Some(get_dummy_raw_channel_end_ics26()),
            signer: get_dummy_bech32_account(),
        }
    }

    pub fn get_dummy_raw_msg_chan_open_init_with_missing_connection() -> RawMsgChannelOpenInit {
        RawMsgChannelOpenInit {
            port_id: "port".to_string(),
            channel: Some(get_dummy_raw_channel_end_with_missing_connection()),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ics04_channel::msgs::chan_open_init::test_util::get_dummy_raw_msg_chan_open_init;
    use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;
    use std::convert::TryFrom;

    #[test]
    fn channel_open_init_from_raw() {
        struct Test {
            name: String,
            raw: RawMsgChannelOpenInit,
            want_pass: bool,
        }

        let default_raw_msg = get_dummy_raw_msg_chan_open_init();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Incorrect port identifier, slash (separator) prohibited".to_string(),
                raw: RawMsgChannelOpenInit {
                    port_id: "p34/".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing channel".to_string(),
                raw: RawMsgChannelOpenInit {
                    channel: None,
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res_msg = MsgChannelOpenInit::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                res_msg.is_ok(),
                "MsgChanOpenInit::try_from failed for test {}, \nraw msg {:?} with error {:?}",
                test.name,
                test.raw,
                res_msg.err(),
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_raw_msg_chan_open_init();
        let msg = MsgChannelOpenInit::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgChannelOpenInit::from(msg.clone());
        let msg_back = MsgChannelOpenInit::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
