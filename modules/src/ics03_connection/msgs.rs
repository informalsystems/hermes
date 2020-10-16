//! Message definitions for the connection handshake datagrams.
//!
//! We define each of the four messages in the connection handshake protocol as a `struct`.
//! Each such message comprises the same fields as the datagrams defined in ICS3 English spec:
//! https://github.com/cosmos/ics/tree/master/spec/ics-003-connection-semantics.
//!
//! One departure from ICS3 is that we abstract the three counterparty fields (connection id,
//! prefix, and client id) into a single field of type `Counterparty`; this applies to messages
//! `MsgConnectionOpenInit` and `MsgConnectionOpenTry`. One other difference with regards to
//! abstraction is that all proof-related attributes in a message are encapsulated in `Proofs` type.
//!
//! Another difference to ICS3 specs is that each message comprises an additional field called
//! `signer` which is specific to Cosmos-SDK.
use crate::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use crate::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;

pub mod conn_open_ack;
pub mod conn_open_confirm;
pub mod conn_open_init;
pub mod conn_open_try;

/// Message type for the `MsgConnectionOpenConfirm` message.
pub const TYPE_MSG_CONNECTION_OPEN_CONFIRM: &str = "connection_open_confirm";

/// Enumeration of all possible messages that the ICS3 protocol processes.
#[derive(Clone, Debug)]
pub enum ConnectionMsg {
    ConnectionOpenInit(MsgConnectionOpenInit),
    ConnectionOpenTry(Box<MsgConnectionOpenTry>),
    ConnectionOpenAck(MsgConnectionOpenAck),
    ConnectionOpenConfirm(MsgConnectionOpenConfirm),
}

#[cfg(test)]
pub mod test_util {
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    use ibc_proto::ibc::core::commitment::v1::MerklePrefix;
    use ibc_proto::ibc::core::connection::v1::Counterparty as RawCounterparty;

    pub fn get_dummy_proof() -> Vec<u8> {
        "Y29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIy"
            .as_bytes()
            .to_vec()
    }

    pub fn get_dummy_account_id_raw() -> String {
        "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C".to_string()
    }

    pub fn get_dummy_account_id() -> AccountId {
        AccountId::from_str(&get_dummy_account_id_raw()).unwrap()
    }

    pub fn get_dummy_counterparty() -> RawCounterparty {
        RawCounterparty {
            client_id: "destclient".to_string(),
            connection_id: "destconnection".to_string(),
            prefix: Some(MerklePrefix {
                key_prefix: b"ibc".to_vec(),
            }),
        }
    }
}
