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
use crate::ics03_connection::connection::{validate_version, validate_versions, Counterparty};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics23_commitment::{CommitmentPrefix, CommitmentProof};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::proofs::{ConsensusProof, Proofs};
use crate::tx_msg::Msg;
use serde_derive::{Deserialize, Serialize};
use tendermint::account::Id as AccountId;
use tendermint::block::Height;

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
    // ConnectionOpenTry(MsgConnectionOpenTry),
    // ConnectionOpenAck(MsgConnectionOpenAck),
    // ConnectionOpenConfirm(MsgConnectionOpenConfirm),
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
    pub fn new(
        connection_id: String,
        client_id: String,
        counterparty_connection_id: String,
        counterparty_client_id: String,
        counterparty_commitment_prefix: CommitmentPrefix,
        signer: AccountId,
    ) -> Result<MsgConnectionOpenInit, Error> {
        Ok(Self {
            connection_id: connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_id: client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty: Counterparty::new(
                counterparty_client_id,
                counterparty_connection_id,
                counterparty_commitment_prefix,
            )
            .map_err(|e| Kind::IdentifierError.context(e))?,
            signer,
        })
    }

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
    counterparty: Counterparty,
    counterparty_versions: Vec<String>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgConnectionOpenTry {
    pub fn new(
        connection_id: String,
        client_id: String,
        counterparty_connection_id: String,
        counterparty_client_id: String,
        counterparty_commitment_prefix: CommitmentPrefix,
        counterparty_versions: Vec<String>,
        init_proof: CommitmentProof,
        consensus_proof: CommitmentProof,
        proofs_height: u64,
        consensus_height: u64,
        signer: AccountId,
    ) -> Result<MsgConnectionOpenTry, Error> {
        let consensus_proof_obj = ConsensusProof::new(consensus_proof, consensus_height)
            .map_err(|e| Kind::InvalidProof.context(e))?;

        Ok(Self {
            connection_id: connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_id: client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty: Counterparty::new(
                counterparty_client_id,
                counterparty_connection_id,
                counterparty_commitment_prefix,
            )
            .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_versions: validate_versions(counterparty_versions)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(init_proof, Option::from(consensus_proof_obj), proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }

    /// Getter for accessing the `consensus_height` field from this message. Returns the special
    /// value `0` if this field is not set.
    pub fn consensus_height(&self) -> Height {
        match self.proofs.consensus_proof() {
            None => Height(0),
            Some(p) => p.height(),
        }
    }

    /// Getter for accesing the whole counterparty of this message. Returns a `clone()`.
    pub fn counterparty(&self) -> Counterparty {
        self.counterparty.clone()
    }

    /// Getter for accessing the client identifier from this message.
    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    /// Getter for accessing the connection identifier of this message.
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    /// Getter for accessing the proofs in this message.
    pub fn proofs(&self) -> &Proofs {
        &self.proofs
    }

    /// Getter for accessing the versions from this message. Returns a `clone()`.
    pub fn counterparty_versions(&self) -> Vec<String> {
        self.counterparty_versions.clone()
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

///
/// Message definition `MsgConnectionOpenAck`  (i.e., `ConnOpenAck` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenAck {
    connection_id: ConnectionId,
    proofs: Proofs,
    version: String,
    signer: AccountId,
}

impl MsgConnectionOpenAck {
    pub fn new(
        connection_id: String,
        proof_try: CommitmentProof,
        proof_consensus: CommitmentProof,
        proofs_height: u64,
        consensus_height: u64,
        version: String,
        signer: AccountId,
    ) -> Result<MsgConnectionOpenAck, Error> {
        let consensus_proof_obj = ConsensusProof::new(proof_consensus, consensus_height)
            .map_err(|e| Kind::InvalidProof.context(e))?;

        Ok(Self {
            connection_id: connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proofs: Proofs::new(proof_try, Option::from(consensus_proof_obj), proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            version: validate_version(version).map_err(|e| Kind::InvalidVersion.context(e))?,
            signer,
        })
    }

    /// Getter for accessing the `consensus_height` field from this message. Returns the special
    /// value `0` if this field is not set.
    pub fn consensus_height(&self) -> Height {
        match self.proofs.consensus_proof() {
            None => Height(0),
            Some(p) => p.height(),
        }
    }

    /// Getter for accessing the connection identifier of this message.
    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    /// Getter for the version field.
    pub fn version(&self) -> &String {
        &self.version
    }

    /// Getter for accessing (borrow) the proofs in this message.
    pub fn proofs(&self) -> &Proofs {
        &self.proofs
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
    pub fn new(
        connection_id: String,
        proof_ack: CommitmentProof,
        proofs_height: u64,
        signer: AccountId,
    ) -> Result<MsgConnectionOpenConfirm, Error> {
        Ok(Self {
            connection_id: connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proofs: Proofs::new(proof_ack, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }

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

#[cfg(test)]
pub mod test_util {
    use crate::ics03_connection::msgs::MsgConnectionOpenInit;
    use crate::ics23_commitment::{CommitmentPrefix, CommitmentProof};
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;
    use tendermint::merkle::proof::ProofOp;

    pub fn get_dummy_proof() -> CommitmentProof {
        let proof_op = ProofOp {
            field_type: "iavl:v".to_string(),
            key: "Y29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIy".as_bytes().to_vec(),
            data: "8QEK7gEKKAgIEAwYHCIgG9RAkJgHlxNjmyzOW6bUAidhiRSja0x6+GXCVENPG1oKKAgGEAUYFyIgwRns+dJvjf1Zk2BaFrXz8inPbvYHB7xx2HCy9ima5f8KKAgEEAMYFyogOr8EGajEV6fG5fzJ2fAAvVMgRLhdMJTzCPlogl9rxlIKKAgCEAIYFyIgcjzX/a+2bFbnNldpawQqZ+kYhIwz5r4wCUzuu1IFW04aRAoeY29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIyEiAZ1uuG60K4NHJZZMuS9QX6o4eEhica5jIHYwflRiYkDBgX"
                .as_bytes().to_vec()
        };

        CommitmentProof {
            ops: vec![proof_op],
        }
    }

    pub fn get_dummy_account_id() -> AccountId {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        AccountId::from_str(id_hex).unwrap()
    }

    /// Returns a dummy message, for testing only.
    /// Other unit tests may import this if they depend on a MsgConnectionOpenInit.
    pub fn get_dummy_msg_conn_open_init() -> MsgConnectionOpenInit {
        MsgConnectionOpenInit::new(
            "srcconnection".to_string(),
            "srcclient".to_string(),
            "destconnection".to_string(),
            "destclient".to_string(),
            CommitmentPrefix::new(vec![]),
            get_dummy_account_id(),
        )
        .unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::test_util::get_dummy_proof;
    use super::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics03_connection::msgs::{
        MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenTry,
    };
    use crate::ics23_commitment::{CommitmentPrefix, CommitmentProof};

    #[test]
    fn parse_connection_open_init_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct ConnOpenInitParams {
            connection_id: String,
            client_id: String,
            counterparty_connection_id: String,
            counterparty_client_id: String,
            counterparty_commitment_prefix: CommitmentPrefix,
        }

        struct Test {
            name: String,
            params: ConnOpenInitParams,
            want_pass: bool,
        }

        let default_con_params = ConnOpenInitParams {
            connection_id: "srcconnection".to_string(),
            client_id: "srcclient".to_string(),
            counterparty_connection_id: "destconnection".to_string(),
            counterparty_client_id: "destclient".to_string(),
            counterparty_commitment_prefix: CommitmentPrefix::new(vec![]),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                params: ConnOpenInitParams {
                    connection_id: "con007".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, name too short".to_string(),
                params: ConnOpenInitParams {
                    client_id: "client".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad destination connection id, name too long".to_string(),
                params: ConnOpenInitParams {
                    counterparty_connection_id:
                        "abcdefghijksdffjssdkflweldflsfladfsfwjkrekcmmsdfsdfjflddmnopqrstu"
                            .to_string(),
                    ..default_con_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let acc = get_dummy_account_id();

            let msg = MsgConnectionOpenInit::new(
                p.connection_id,
                p.client_id,
                p.counterparty_connection_id,
                p.counterparty_client_id,
                p.counterparty_commitment_prefix,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenInit::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_connection_open_try_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct ConOpenTryParams {
            connection_id: String,
            client_id: String,
            counterparty_connection_id: String,
            counterparty_client_id: String,
            counterparty_commitment_prefix: CommitmentPrefix,
            counterparty_versions: Vec<String>,
            proof_init: CommitmentProof,
            proof_consensus: CommitmentProof,
            proof_height: u64,
            consensus_height: u64,
        }

        struct Test {
            name: String,
            params: ConOpenTryParams,
            want_pass: bool,
        }

        let default_con_params = ConOpenTryParams {
            connection_id: "srcconnection".to_string(),
            client_id: "srcclient".to_string(),
            counterparty_connection_id: "destconnection".to_string(),
            counterparty_client_id: "destclient".to_string(),
            counterparty_commitment_prefix: CommitmentPrefix::new(vec![]),
            counterparty_versions: vec!["1.0.0".to_string()],
            proof_init: get_dummy_proof(),
            proof_consensus: get_dummy_proof(),
            proof_height: 10,
            consensus_height: 10,
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                params: ConOpenTryParams {
                    connection_id: "con007".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, name too short".to_string(),
                params: ConOpenTryParams {
                    client_id: "client".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad destination connection id, name too long".to_string(),
                params: ConOpenTryParams {
                    counterparty_connection_id:
                        "abcdasdfasdfsdfasfdwefwfsdfsfsfasfwewvxcvdvwgadvaadsefghijklmnopqrstu"
                            .to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct destination client id with lower/upper case and special chars"
                    .to_string(),
                params: ConOpenTryParams {
                    counterparty_client_id: "ClientId_".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad counterparty versions, empty versions vec".to_string(),
                params: ConOpenTryParams {
                    counterparty_versions: vec![],
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad counterparty versions, empty version string".to_string(),
                params: ConOpenTryParams {
                    counterparty_versions: vec!["".to_string()],
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height is 0".to_string(),
                params: ConOpenTryParams {
                    proof_height: 0,
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad consensus height, height is 0".to_string(),
                params: ConOpenTryParams {
                    consensus_height: 0,
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof".to_string(),
                params: ConOpenTryParams {
                    proof_init: CommitmentProof { ops: vec![] },
                    ..default_con_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let acc = get_dummy_account_id();

            let msg = MsgConnectionOpenTry::new(
                p.connection_id,
                p.client_id,
                p.counterparty_connection_id,
                p.counterparty_client_id,
                p.counterparty_commitment_prefix,
                p.counterparty_versions,
                p.proof_init,
                p.proof_consensus,
                p.proof_height,
                p.consensus_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenTry::new failed for test {}, \nmsg {:?} \nwith error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_connection_open_ack_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct ConOpenAckParams {
            connection_id: String,
            proof_try: CommitmentProof,
            proof_consensus: CommitmentProof,
            proof_height: u64,
            consensus_height: u64,
            version: String,
        }

        struct Test {
            name: String,
            params: ConOpenAckParams,
            want_pass: bool,
        }

        let default_con_params = ConOpenAckParams {
            connection_id: "srcconnection".to_string(),
            proof_try: get_dummy_proof(),
            proof_consensus: get_dummy_proof(),
            proof_height: 10,
            consensus_height: 10,
            version: "1.0.0".to_string(),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                params: ConOpenAckParams {
                    connection_id: "con007".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad version, empty version string".to_string(),
                params: ConOpenAckParams {
                    version: "".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height is 0".to_string(),
                params: ConOpenAckParams {
                    proof_height: 0,
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad consensus height, height is 0".to_string(),
                params: ConOpenAckParams {
                    consensus_height: 0,
                    ..default_con_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let acc = get_dummy_account_id();

            let msg = MsgConnectionOpenAck::new(
                p.connection_id,
                p.proof_try,
                p.proof_consensus,
                p.proof_height,
                p.consensus_height,
                p.version,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenAck::new failed for test {}, \nmsg {:?} \nwith error {:?}",
                test.name,
                test.params.clone(),
                msg.err()
            );
        }
    }

    #[test]
    fn parse_connection_open_confirm_msg() {
        #[derive(Clone, Debug, PartialEq)]
        struct ConOpenConfirmParams {
            connection_id: String,
            proof_ack: CommitmentProof,
            proof_height: u64,
        }

        struct Test {
            name: String,
            params: ConOpenConfirmParams,
            want_pass: bool,
        }

        let default_con_params = ConOpenConfirmParams {
            connection_id: "srcconnection".to_string(),
            proof_ack: get_dummy_proof(),
            proof_height: 10,
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                params: ConOpenConfirmParams {
                    connection_id: "con007".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height is 0".to_string(),
                params: ConOpenConfirmParams {
                    proof_height: 0,
                    ..default_con_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let acc = get_dummy_account_id();

            let msg =
                MsgConnectionOpenConfirm::new(p.connection_id, p.proof_ack, p.proof_height, acc);

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgConnOpenConfirm::new failed for test {}, \nmsg {:?} \nwith error {:?}",
                test.name,
                test.params.clone(),
                msg.err()
            );
        }
    }
}
