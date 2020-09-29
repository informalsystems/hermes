use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::str::{from_utf8, FromStr};

use ibc_proto::ibc::connection::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
use tendermint::account::Id as AccountId;
use tendermint::block::Height;

use crate::ics02_client::client_def::AnyClientState;
use crate::ics03_connection::connection::validate_version;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics24_host::identifier::ConnectionId;
use crate::proofs::{ConsensusProof, Proofs};
use crate::tx_msg::Msg;

/// Message type for the `MsgConnectionOpenAck` message.
pub const TYPE_MSG_CONNECTION_OPEN_ACK: &str = "connection_open_ack";

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

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::client::Height;
    use ibc_proto::ibc::connection::MsgConnectionOpenAck as RawMsgConnectionOpenAck;

    use crate::ics03_connection::msgs::test_util::{get_dummy_account_id_bytes, get_dummy_proof};

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
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::client::Height;
    use ibc_proto::ibc::connection::MsgConnectionOpenAck as RawMsgConnectionOpenAck;

    use crate::ics03_connection::msgs::conn_open_ack::test_util::get_dummy_msg_conn_open_ack;
    use crate::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;

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
}
