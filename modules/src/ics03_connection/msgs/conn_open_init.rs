use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use tendermint_proto::Protobuf;

use tendermint::account::Id as AccountId;

use crate::address::{account_to_string, string_to_account};
use crate::ics03_connection::connection::Counterparty;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::version::validate_version;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::tx_msg::Msg;

/// Message type for the `MsgConnectionOpenInit` message.
pub const TYPE_MSG_CONNECTION_OPEN_INIT: &str = "connection_open_init";
///
/// Message definition `MsgConnectionOpenInit`  (i.e., the `ConnOpenInit` datagram).
///
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgConnectionOpenInit {
    pub connection_id: ConnectionId,
    pub client_id: ClientId,
    pub counterparty: Counterparty,
    pub version: String,
    pub signer: AccountId,
}

impl MsgConnectionOpenInit {
    /// Getter: borrow the `connection_id` from this message.
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    /// Getter: borrow the `client_id` from this message.
    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    /// Getter: borrow the `counterparty` from this message.
    pub fn counterparty(&self) -> &Counterparty {
        &self.counterparty
    }

    /// Setter for `client_id`. Amenable to chaining, since it consumes the input message.
    pub fn with_client_id(self, client_id: ClientId) -> Self {
        MsgConnectionOpenInit { client_id, ..self }
    }
}

impl Msg for MsgConnectionOpenInit {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CONNECTION_OPEN_INIT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // All the validation is performed on creation
        self.counterparty
            .validate_basic()
            .map_err(|e| Kind::InvalidCounterparty.context(e).into())
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }

    fn type_url(&self) -> String {
        "/ibc.core.connection.v1.MsgConnectionOpenInit".to_string()
    }
}

impl Protobuf<RawMsgConnectionOpenInit> for MsgConnectionOpenInit {}

impl TryFrom<RawMsgConnectionOpenInit> for MsgConnectionOpenInit {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenInit) -> Result<Self, Self::Error> {
        let signer = string_to_account(msg.signer).map_err(|e| Kind::InvalidAddress.context(e))?;

        Ok(Self {
            connection_id: msg
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_id: msg
                .client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty: msg
                .counterparty
                .ok_or_else(|| Kind::MissingCounterparty)?
                .try_into()?,
            version: validate_version(msg.version).map_err(|e| Kind::InvalidVersion.context(e))?,
            signer,
        })
    }
}

impl From<MsgConnectionOpenInit> for RawMsgConnectionOpenInit {
    fn from(ics_msg: MsgConnectionOpenInit) -> Self {
        RawMsgConnectionOpenInit {
            client_id: ics_msg.client_id.as_str().to_string(),
            connection_id: ics_msg.connection_id.as_str().to_string(),
            counterparty: Some(ics_msg.counterparty.into()),
            version: ics_msg.version,
            signer: account_to_string(ics_msg.signer).unwrap(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;

    use crate::ics03_connection::msgs::test_util::get_dummy_counterparty;
    use crate::ics03_connection::version::default_version_string;
    use crate::test_utils::get_dummy_bech32_account;

    /// Returns a dummy message, for testing only.
    /// Other unit tests may import this if they depend on a MsgConnectionOpenInit.
    pub fn get_dummy_msg_conn_open_init() -> RawMsgConnectionOpenInit {
        RawMsgConnectionOpenInit {
            client_id: "srcclient".to_string(),
            connection_id: "srcconnection".to_string(),
            counterparty: Some(get_dummy_counterparty()),
            version: default_version_string(),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::core::connection::v1::Counterparty as RawCounterparty;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;

    use super::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::test_util::get_dummy_counterparty;

    #[test]
    fn parse_connection_open_init_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct Test {
            name: String,
            raw: RawMsgConnectionOpenInit,
            want_pass: bool,
        }

        let default_init_msg = get_dummy_msg_conn_open_init();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_init_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                raw: RawMsgConnectionOpenInit {
                    connection_id: "con007".to_string(),
                    ..default_init_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, name too short".to_string(),
                raw: RawMsgConnectionOpenInit {
                    client_id: "client".to_string(),
                    ..default_init_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad destination connection id, name too long".to_string(),
                raw: RawMsgConnectionOpenInit {
                    counterparty: Some(RawCounterparty {
                        connection_id:
                            "abcdefghijksdffjssdkflweldflsfladfsfwjkrekcmmsdfsdfjflddmnopqrstu"
                                .to_string(),
                        ..get_dummy_counterparty()
                    }),
                    ..default_init_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let msg = MsgConnectionOpenInit::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenInit::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.raw,
                msg.err(),
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_msg_conn_open_init();
        let msg = MsgConnectionOpenInit::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgConnectionOpenInit::from(msg.clone());
        let msg_back = MsgConnectionOpenInit::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
