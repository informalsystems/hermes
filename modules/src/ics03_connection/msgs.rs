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
//! TODO: Separate the Cosmos-SDK specific functionality from canonical ICS types. Decorators?

#![allow(clippy::too_many_arguments)]

use crate::ics02_client::client_def::AnyClientState;
use crate::ics03_connection::connection::{validate_version, validate_versions, Counterparty};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::proofs::{ConsensusProof, Proofs};
use crate::tx_msg::Msg;

use ibc_proto::ibc::connection::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
use ibc_proto::ibc::connection::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
use ibc_proto::ibc::connection::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use ibc_proto::ibc::connection::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

use tendermint::account::Id as AccountId;
use tendermint::block::Height;

use serde_derive::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};
use std::str::{from_utf8, FromStr};
use tendermint_proto::DomainType;

/// Message type for the `MsgConnectionOpenInit` message.
pub const TYPE_MSG_CONNECTION_OPEN_INIT: &str = "connection_open_init";

/// Message type for the `MsgConnectionOpenTry` message.
pub const TYPE_MSG_CONNECTION_OPEN_TRY: &str = "connection_open_try";

/// Message type for the `MsgConnectionOpenAck` message.
pub const TYPE_MSG_CONNECTION_OPEN_ACK: &str = "connection_open_ack";

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

///
/// Message definition `MsgConnectionOpenInit`  (i.e., the `ConnOpenInit` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenInit {
    connection_id: ConnectionId,
    client_id: ClientId,
    counterparty: Counterparty,
    signer: AccountId,
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
}

impl DomainType<RawMsgConnectionOpenInit> for MsgConnectionOpenInit {}

impl TryFrom<RawMsgConnectionOpenInit> for MsgConnectionOpenInit {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenInit) -> Result<Self, Self::Error> {
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
            signer: AccountId::from_str(
                from_utf8(&msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?,
            )
            .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

impl From<MsgConnectionOpenInit> for RawMsgConnectionOpenInit {
    fn from(value: MsgConnectionOpenInit) -> Self {
        RawMsgConnectionOpenInit {
            client_id: value.client_id.as_str().to_string(),
            connection_id: value.connection_id.as_str().to_string(),
            counterparty: Some(value.counterparty.into()),
            signer: value.signer.as_bytes().to_vec(),
        }
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
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

///
/// Message definition `MsgConnectionOpenTry`  (i.e., `ConnOpenTry` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenTry {
    connection_id: ConnectionId,
    client_id: ClientId,
    client_state: Option<AnyClientState>,
    counterparty: Counterparty,
    counterparty_versions: Vec<String>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgConnectionOpenTry {
    /// Getter for accessing the connection identifier of this message.
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    /// Getter for accessing the client identifier from this message.
    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    /// Getter for accessing the client state.
    pub fn client_state(&self) -> Option<AnyClientState> {
        self.client_state.clone()
    }

    /// Getter for accesing the whole counterparty of this message. Returns a `clone()`.
    pub fn counterparty(&self) -> Counterparty {
        self.counterparty.clone()
    }

    /// Getter for accessing the versions from this message. Returns a `clone()`.
    pub fn counterparty_versions(&self) -> Vec<String> {
        self.counterparty_versions.clone()
    }

    /// Getter for accessing the proofs in this message.
    pub fn proofs(&self) -> &Proofs {
        &self.proofs
    }

    /// Getter for accessing the `consensus_height` field from this message. Returns the special
    /// value `0` if this field is not set.
    pub fn consensus_height(&self) -> Height {
        match self.proofs.consensus_proof() {
            None => Height(0),
            Some(p) => p.height(),
        }
    }
}

impl Msg for MsgConnectionOpenTry {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CONNECTION_OPEN_TRY.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.counterparty
            .validate_basic()
            .map_err(|e| Kind::InvalidCounterparty.context(e).into())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl TryFrom<RawMsgConnectionOpenTry> for MsgConnectionOpenTry {
    type Error = Error;

    fn try_from(msg: RawMsgConnectionOpenTry) -> Result<Self, Self::Error> {
        let proof_height = msg
            .proof_height
            .ok_or_else(|| Kind::MissingProofHeight)?
            .epoch_height; // FIXME: This is wrong as it does not take the epoch number into account
        let consensus_height = msg
            .consensus_height
            .ok_or_else(|| Kind::MissingConsensusHeight)?
            .epoch_height; // FIXME: This is wrong as it does not take the epoch number into account
        let consensus_proof_obj = ConsensusProof::new(msg.proof_consensus.into(), consensus_height)
            .map_err(|e| Kind::InvalidProof.context(e))?;

        let client_proof = match msg.client_state {
            None => None,
            Some(_) => Some(msg.proof_client.into()),
        };

        Ok(Self {
            connection_id: msg
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_id: msg
                .client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_state: msg
                .client_state
                .map(AnyClientState::try_from)
                .transpose()
                .map_err(|e| Kind::InvalidProof.context(e))?,
            counterparty: msg
                .counterparty
                .ok_or_else(|| Kind::MissingCounterparty)?
                .try_into()?,
            counterparty_versions: validate_versions(msg.counterparty_versions)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(
                msg.proof_init.into(),
                client_proof,
                Some(consensus_proof_obj),
                proof_height,
            )
            .map_err(|e| Kind::InvalidProof.context(e))?,
            signer: AccountId::from_str(
                from_utf8(&msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?,
            )
            .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

///
/// Message definition `MsgConnectionOpenAck`  (i.e., `ConnOpenAck` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenAck {
    connection_id: ConnectionId,
    client_state: Option<AnyClientState>,
    proofs: Proofs,
    version: String,
    signer: AccountId,
}

impl MsgConnectionOpenAck {
    /// Getter for accessing the connection identifier of this message.
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    /// Getter for accessing the client state.
    pub fn client_state(&self) -> Option<AnyClientState> {
        self.client_state.clone()
    }

    /// Getter for accessing (borrow) the proofs in this message.
    pub fn proofs(&self) -> &Proofs {
        &self.proofs
    }

    /// Getter for the version field.
    pub fn version(&self) -> &String {
        &self.version
    }

    /// Getter for accessing the `consensus_height` field from this message. Returns the special
    /// value `0` if this field is not set.
    pub fn consensus_height(&self) -> Height {
        match self.proofs.consensus_proof() {
            None => Height(0),
            Some(p) => p.height(),
        }
    }
}

impl Msg for MsgConnectionOpenAck {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CONNECTION_OPEN_ACK.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl TryFrom<RawMsgConnectionOpenAck> for MsgConnectionOpenAck {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenAck) -> Result<Self, Self::Error> {
        let proof_height = msg
            .proof_height
            .ok_or_else(|| Kind::MissingProofHeight)?
            .epoch_height; // FIXME: This is wrong as it does not take the epoch number into account
        let consensus_height = msg
            .consensus_height
            .ok_or_else(|| Kind::MissingConsensusHeight)?
            .epoch_height; // FIXME: This is wrong as it does not take the epoch number into account
        let consensus_proof_obj = ConsensusProof::new(msg.proof_consensus.into(), consensus_height)
            .map_err(|e| Kind::InvalidProof.context(e))?;

        let client_proof = match msg.client_state {
            None => None,
            Some(_) => Some(msg.proof_client.into()),
        };

        Ok(Self {
            connection_id: msg
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_state: msg
                .client_state
                .map(AnyClientState::try_from)
                .transpose()
                .map_err(|e| Kind::InvalidProof.context(e))?,
            version: validate_version(msg.version).map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(
                msg.proof_try.into(),
                client_proof,
                Option::from(consensus_proof_obj),
                proof_height,
            )
            .map_err(|e| Kind::InvalidProof.context(e))?,
            signer: AccountId::from_str(
                from_utf8(&msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?,
            )
            .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

///
/// Message definition for `MsgConnectionOpenConfirm` (i.e., `ConnOpenConfirm` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenConfirm {
    connection_id: ConnectionId,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgConnectionOpenConfirm {
    /// Getter for accessing the connection identifier of this message.
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    /// Getter for accessing (borrow) the proofs in this message.
    pub fn proofs(&self) -> &Proofs {
        &self.proofs
    }
}

impl Msg for MsgConnectionOpenConfirm {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CONNECTION_OPEN_CONFIRM.to_string()
    }

    fn validate_basic(&self) -> Result<(), Error> {
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl TryFrom<RawMsgConnectionOpenConfirm> for MsgConnectionOpenConfirm {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenConfirm) -> Result<Self, Self::Error> {
        let proof_height = msg
            .proof_height
            .ok_or_else(|| Kind::MissingProofHeight)?
            .epoch_height; // FIXME: This is wrong as it does not take the epoch number into account
        Ok(Self {
            connection_id: msg
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proofs: Proofs::new(msg.proof_ack.into(), None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer: AccountId::from_str(
                from_utf8(&msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?,
            )
            .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

#[cfg(test)]
pub mod test_util {
    use std::str::{from_utf8, FromStr};
    use tendermint::account::Id as AccountId;

    use ibc_proto::ibc::client::Height;
    use ibc_proto::ibc::commitment::MerklePrefix;
    use ibc_proto::ibc::connection::Counterparty as RawCounterparty;
    use ibc_proto::ibc::connection::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
    use ibc_proto::ibc::connection::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
    use ibc_proto::ibc::connection::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
    use ibc_proto::ibc::connection::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

    pub fn get_dummy_proof() -> Vec<u8> {
        "Y29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIy"
            .as_bytes()
            .to_vec()
    }

    pub fn get_dummy_account_id_bytes() -> Vec<u8> {
        "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C"
            .as_bytes()
            .to_vec()
    }

    pub fn get_dummy_account_id() -> AccountId {
        AccountId::from_str(from_utf8(&get_dummy_account_id_bytes()).unwrap()).unwrap()
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

    /// Returns a dummy message, for testing only.
    /// Other unit tests may import this if they depend on a MsgConnectionOpenInit.
    pub fn get_dummy_msg_conn_open_init() -> RawMsgConnectionOpenInit {
        RawMsgConnectionOpenInit {
            client_id: "srcclient".to_string(),
            connection_id: "srcconnection".to_string(),
            counterparty: Some(get_dummy_counterparty()),
            signer: get_dummy_account_id_bytes(),
        }
    }

    pub fn get_dummy_msg_conn_open_try(
        proof_height: u64,
        consensus_height: u64,
    ) -> RawMsgConnectionOpenTry {
        RawMsgConnectionOpenTry {
            client_id: "srcclient".to_string(),
            connection_id: "srcconnection".to_string(),
            client_state: None,
            counterparty: Some(get_dummy_counterparty()),
            counterparty_versions: vec!["1.0.0".to_string()],
            proof_init: get_dummy_proof(),
            proof_height: Some(Height {
                epoch_number: 1,
                epoch_height: proof_height,
            }),
            proof_consensus: get_dummy_proof(),
            consensus_height: Some(Height {
                epoch_number: 1,
                epoch_height: consensus_height,
            }),
            signer: get_dummy_account_id_bytes(),
            proof_client: vec![],
        }
    }

    pub fn get_dummy_msg_conn_open_ack() -> RawMsgConnectionOpenAck {
        RawMsgConnectionOpenAck {
            connection_id: "srcconnection".to_string(),
            version: "1.0.0".to_string(),
            proof_try: get_dummy_proof(),
            proof_height: Some(Height {
                epoch_number: 1,
                epoch_height: 10,
            }),
            proof_consensus: get_dummy_proof(),
            consensus_height: Some(Height {
                epoch_number: 1,
                epoch_height: 10,
            }),
            signer: get_dummy_account_id_bytes(),
            client_state: None,
            proof_client: vec![],
        }
    }

    pub fn get_dummy_msg_conn_open_confirm() -> RawMsgConnectionOpenConfirm {
        RawMsgConnectionOpenConfirm {
            connection_id: "srcconnection".to_string(),
            proof_ack: get_dummy_proof(),
            proof_height: Some(Height {
                epoch_number: 1,
                epoch_height: 10,
            }),
            signer: get_dummy_account_id_bytes(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::client::Height;
    use ibc_proto::ibc::connection::Counterparty as RawCounterparty;
    use ibc_proto::ibc::connection::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
    use ibc_proto::ibc::connection::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
    use ibc_proto::ibc::connection::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
    use ibc_proto::ibc::connection::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

    use super::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::test_util::{
        get_dummy_counterparty, get_dummy_msg_conn_open_ack, get_dummy_msg_conn_open_confirm,
        get_dummy_msg_conn_open_init, get_dummy_msg_conn_open_try,
    };
    use crate::ics03_connection::msgs::{
        MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenTry,
    };

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
    fn parse_connection_open_try_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct Test {
            name: String,
            raw: RawMsgConnectionOpenTry,
            want_pass: bool,
        }

        let default_try_msg = get_dummy_msg_conn_open_try(10, 34);

        let tests: Vec<Test> =
            vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_try_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                raw: RawMsgConnectionOpenTry {
                    connection_id: "con007".to_string(),
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, name too short".to_string(),
                raw: RawMsgConnectionOpenTry {
                    client_id: "client".to_string(),
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad destination connection id, name too long".to_string(),
                raw: RawMsgConnectionOpenTry {
                    counterparty: Some(RawCounterparty {
                        connection_id:
                            "abcdasdfasdfsdfasfdwefwfsdfsfsfasfwewvxcvdvwgadvaadsefghijklmnopqrstu"
                                .to_string(),
                        ..get_dummy_counterparty()
                    }),
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct destination client id with lower/upper case and special chars"
                    .to_string(),
                raw: RawMsgConnectionOpenTry {
                    counterparty: Some(RawCounterparty {
                        client_id: "ClientId_".to_string(),
                        ..get_dummy_counterparty()
                    }),
                    ..default_try_msg.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad counterparty versions, empty versions vec".to_string(),
                raw: RawMsgConnectionOpenTry {
                    counterparty_versions: vec![],
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad counterparty versions, empty version string".to_string(),
                raw: RawMsgConnectionOpenTry {
                    counterparty_versions: vec!["".to_string()],
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height is 0".to_string(),
                raw: RawMsgConnectionOpenTry {
                    proof_height: Some(Height{ epoch_number: 1, epoch_height: 0 }),
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad consensus height, height is 0".to_string(),
                raw: RawMsgConnectionOpenTry {
                    proof_height: Some(Height{ epoch_number: 1, epoch_height: 0 }),
                    ..default_try_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof".to_string(),
                raw: RawMsgConnectionOpenTry {
                    proof_init: b"".to_vec(),
                    ..default_try_msg
                },
                want_pass: false,
            }
            ]
            .into_iter()
            .collect();

        for test in tests {
            let msg = MsgConnectionOpenTry::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenTry::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.raw,
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_connection_open_ack_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct Test {
            name: String,
            raw: RawMsgConnectionOpenAck,
            want_pass: bool,
        }

        let default_ack_msg = get_dummy_msg_conn_open_ack();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_ack_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                raw: RawMsgConnectionOpenAck {
                    connection_id: "con007".to_string(),
                    ..default_ack_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad version, empty version string".to_string(),
                raw: RawMsgConnectionOpenAck {
                    version: "".to_string(),
                    ..default_ack_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height is 0".to_string(),
                raw: RawMsgConnectionOpenAck {
                    proof_height: Some(Height {
                        epoch_number: 1,
                        epoch_height: 0,
                    }),
                    ..default_ack_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad consensus height, height is 0".to_string(),
                raw: RawMsgConnectionOpenAck {
                    consensus_height: Some(Height {
                        epoch_number: 1,
                        epoch_height: 0,
                    }),
                    ..default_ack_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let msg = MsgConnectionOpenAck::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenTry::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.raw,
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_connection_open_confirm_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct Test {
            name: String,
            raw: RawMsgConnectionOpenConfirm,
            want_pass: bool,
        }

        let default_ack_msg = get_dummy_msg_conn_open_confirm();
        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_ack_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                raw: RawMsgConnectionOpenConfirm {
                    connection_id: "con007".to_string(),
                    ..default_ack_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height is 0".to_string(),
                raw: RawMsgConnectionOpenConfirm {
                    proof_height: Some(Height {
                        epoch_number: 1,
                        epoch_height: 0,
                    }),
                    ..default_ack_msg
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let msg = MsgConnectionOpenConfirm::try_from(test.raw.clone());

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenTry::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.raw,
                msg.err(),
            );
        }
    }
}
