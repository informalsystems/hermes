use serde_derive::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;
use tendermint_proto::DomainType;

use tendermint::account::Id as AccountId;
use tendermint::block::Height;

use crate::ics02_client::client_def::AnyClientState;
use crate::ics03_connection::connection::{validate_versions, Counterparty};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::proofs::{ConsensusProof, Proofs};
use crate::tx_msg::Msg;
use std::str::FromStr;

/// Message type for the `MsgConnectionOpenTry` message.
pub const TYPE_MSG_CONNECTION_OPEN_TRY: &str = "connection_open_try";

///
/// Message definition `MsgConnectionOpenTry`  (i.e., `ConnOpenTry` datagram).
///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenTry {
    connection_id: ConnectionId,
    client_id: ClientId,
    client_state: Option<AnyClientState>,
    counterparty_chosen_connection_id: ConnectionId,
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
            None => Height::from(0_u32),
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

impl DomainType<RawMsgConnectionOpenTry> for MsgConnectionOpenTry {}

impl TryFrom<RawMsgConnectionOpenTry> for MsgConnectionOpenTry {
    type Error = Error;

    fn try_from(msg: RawMsgConnectionOpenTry) -> Result<Self, Self::Error> {
        let proof_height = msg
            .proof_height
            .ok_or_else(|| Kind::MissingProofHeight)?
            .version_height; // FIXME: This is wrong as it does not take the epoch number into account
        let consensus_height = msg
            .consensus_height
            .ok_or_else(|| Kind::MissingConsensusHeight)?
            .version_height; // FIXME: This is wrong as it does not take the epoch number into account
        let consensus_proof_obj = ConsensusProof::new(msg.proof_consensus.into(), consensus_height)
            .map_err(|e| Kind::InvalidProof.context(e))?;

        let client_proof = match msg.client_state {
            None => None,
            Some(_) => Some(msg.proof_client.into()),
        };

        Ok(Self {
            connection_id: msg
                .desired_connection_id
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
            counterparty_chosen_connection_id: msg
                .counterparty_chosen_connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
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
            signer: AccountId::from_str(msg.signer.as_str())
                .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

impl From<MsgConnectionOpenTry> for RawMsgConnectionOpenTry {
    fn from(ics_msg: MsgConnectionOpenTry) -> Self {
        RawMsgConnectionOpenTry {
            client_id: ics_msg.client_id.as_str().to_string(),
            desired_connection_id: ics_msg.connection_id.as_str().to_string(),
            client_state: ics_msg
                .client_state
                .map_or_else(|| None, |v| Some(v.into())),
            counterparty: Some(ics_msg.counterparty.into()),
            counterparty_versions: ics_msg.counterparty_versions,
            counterparty_chosen_connection_id: ics_msg
                .counterparty_chosen_connection_id
                .as_str()
                .to_string(),
            proof_height: Some(ibc_proto::ibc::core::client::v1::Height {
                version_number: 0,
                version_height: ics_msg.proofs.height().value(),
            }),
            proof_init: ics_msg.proofs.object_proof().clone().into(),
            proof_client: ics_msg
                .proofs
                .client_proof()
                .clone()
                .map_or_else(Vec::new, |v| v.into()),
            proof_consensus: ics_msg
                .proofs
                .consensus_proof()
                .map_or_else(Vec::new, |v| v.proof().clone().into()),
            consensus_height: ics_msg.proofs.consensus_proof().map_or_else(
                || None,
                |h| {
                    Some(ibc_proto::ibc::core::client::v1::Height {
                        version_number: 0,
                        version_height: u64::from(h.height()),
                    })
                },
            ),
            signer: ics_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::client::v1::Height;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

    use crate::ics03_connection::msgs::test_util::{
        get_dummy_account_id_raw, get_dummy_counterparty, get_dummy_proof,
    };

    pub fn get_dummy_msg_conn_open_try(
        proof_height: u64,
        consensus_height: u64,
    ) -> RawMsgConnectionOpenTry {
        RawMsgConnectionOpenTry {
            client_id: "srcclient".to_string(),
            desired_connection_id: "srcconnection".to_string(),
            client_state: None,
            counterparty: Some(get_dummy_counterparty()),
            counterparty_versions: vec!["1.0.0".to_string()],
            counterparty_chosen_connection_id: "srcconnection".to_string(),
            proof_init: get_dummy_proof(),
            proof_height: Some(Height {
                version_number: 0,
                version_height: proof_height,
            }),
            proof_consensus: get_dummy_proof(),
            consensus_height: Some(Height {
                version_number: 0,
                version_height: consensus_height,
            }),
            proof_client: vec![],
            signer: get_dummy_account_id_raw(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::core::client::v1::Height;
    use ibc_proto::ibc::core::connection::v1::Counterparty as RawCounterparty;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

    use crate::ics03_connection::msgs::conn_open_try::test_util::get_dummy_msg_conn_open_try;
    use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
    use crate::ics03_connection::msgs::test_util::get_dummy_counterparty;

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
                    name: "Bad desired connection id, non-alpha".to_string(),
                    raw: RawMsgConnectionOpenTry {
                        desired_connection_id: "con007".to_string(),
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
                        proof_height: Some(Height { version_number: 1, version_height: 0 }),
                        ..default_try_msg.clone()
                    },
                    want_pass: false,
                },
                Test {
                    name: "Bad consensus height, height is 0".to_string(),
                    raw: RawMsgConnectionOpenTry {
                        proof_height: Some(Height { version_number: 1, version_height: 0 }),
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
    fn to_and_from() {
        let raw = get_dummy_msg_conn_open_try(10, 34);
        let msg = MsgConnectionOpenTry::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgConnectionOpenTry::from(msg.clone());
        let msg_back = MsgConnectionOpenTry::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
