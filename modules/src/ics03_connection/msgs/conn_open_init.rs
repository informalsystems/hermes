use serde_derive::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use tendermint_proto::DomainType;

use tendermint::account::Id as AccountId;

use crate::ics03_connection::connection::{validate_version, Counterparty};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::tx_msg::Msg;

use bech32::{FromBase32, ToBase32};

/// Message type for the `MsgConnectionOpenInit` message.
pub const TYPE_MSG_CONNECTION_OPEN_INIT: &str = "connection_open_init";
///
/// Message definition `MsgConnectionOpenInit`  (i.e., the `ConnOpenInit` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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

    fn get_sign_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        let raw_msg: RawMsgConnectionOpenInit = self.clone().into();
        prost::Message::encode(&raw_msg, &mut buf).unwrap();
        buf
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl DomainType<RawMsgConnectionOpenInit> for MsgConnectionOpenInit {}

impl TryFrom<RawMsgConnectionOpenInit> for MsgConnectionOpenInit {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenInit) -> Result<Self, Self::Error> {
        let (_hrp, data) = bech32::decode(&msg.signer).map_err(|e| {
            Kind::InvalidAddress
                .context("Error decoding signer ".to_string() + &msg.signer + ":" + &e.to_string())
        })?;
        let addr_bytes = Vec::<u8>::from_base32(&data).map_err(|e| {
            Kind::InvalidAddress
                .context("Error converting from bech32: ".to_string() + &e.to_string())
        })?;
        let acct = AccountId::try_from(addr_bytes).map_err(|e| {
            Kind::InvalidAddress
                .context("Error converting to account ID: ".to_string() + &e.to_string())
        })?;

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
            signer: acct,
        })
    }
}

impl From<MsgConnectionOpenInit> for RawMsgConnectionOpenInit {
    fn from(ics_msg: MsgConnectionOpenInit) -> Self {
        // The msg needs to send the bech32 account as the signer
        let addr = bech32::encode("cosmos", ics_msg.signer.to_base32()).unwrap();
        RawMsgConnectionOpenInit {
            client_id: ics_msg.client_id.as_str().to_string(),
            connection_id: ics_msg.connection_id.as_str().to_string(),
            counterparty: Some(ics_msg.counterparty.into()),
            signer: addr,
            version: ics_msg.version,
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;

    use crate::ics03_connection::msgs::test_util::{
        get_dummy_bech32_account, get_dummy_counterparty,
    };

    /// Returns a dummy message, for testing only.
    /// Other unit tests may import this if they depend on a MsgConnectionOpenInit.
    pub fn get_dummy_msg_conn_open_init() -> RawMsgConnectionOpenInit {
        RawMsgConnectionOpenInit {
            client_id: "srcclient".to_string(),
            connection_id: "srcconnection".to_string(),
            counterparty: Some(get_dummy_counterparty()),
            version: "1.0.0".to_string(),
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
