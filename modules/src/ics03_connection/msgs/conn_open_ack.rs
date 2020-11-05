use std::convert::{TryFrom, TryInto};
use std::str::FromStr;

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
use tendermint_proto::DomainType;

use tendermint::account::Id as AccountId;

use crate::ics02_client::client_def::AnyClientState;
use crate::ics03_connection::connection::validate_version;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::ics24_host::identifier::ConnectionId;
use crate::proofs::{ConsensusProof, Proofs};
use crate::tx_msg::Msg;
use crate::Height;

/// Message type for the `MsgConnectionOpenAck` message.
pub const TYPE_MSG_CONNECTION_OPEN_ACK: &str = "connection_open_ack";

/// Message definition `MsgConnectionOpenAck`  (i.e., `ConnOpenAck` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgConnectionOpenAck {
    connection_id: ConnectionId,
    counterparty_connection_id: Option<ConnectionId>,
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

    /// Getter for accessing the connection identifier of this message.
    pub fn counterparty_connection_id(&self) -> Option<&ConnectionId> {
        self.counterparty_connection_id.as_ref()
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
    /// value `Height(0)` if this field is not set.
    pub fn consensus_height(&self) -> Height {
        match self.proofs.consensus_proof() {
            None => Height::zero(),
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

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl DomainType<RawMsgConnectionOpenAck> for MsgConnectionOpenAck {}

impl TryFrom<RawMsgConnectionOpenAck> for MsgConnectionOpenAck {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenAck) -> Result<Self, Self::Error> {
        let consensus_height = msg
            .consensus_height
            .ok_or_else(|| Kind::MissingConsensusHeight)?
            .try_into() // Cast from the raw height type into the domain type.
            .map_err(|e| Kind::InvalidProof.context(e))?;
        let consensus_proof_obj = ConsensusProof::new(msg.proof_consensus.into(), consensus_height)
            .map_err(|e| Kind::InvalidProof.context(e))?;

        let proof_height = msg
            .proof_height
            .ok_or_else(|| Kind::MissingProofHeight)?
            .try_into()
            .map_err(|e| Kind::InvalidProof.context(e))?;

        let client_proof = Some(msg.proof_client)
            .filter(|x| !x.is_empty())
            .map(CommitmentProof::from);

        let counterparty_connection_id = Some(msg.counterparty_connection_id)
            .filter(|x| !x.is_empty())
            .map(|v| FromStr::from_str(v.as_str()))
            .transpose()
            .map_err(|e| Kind::IdentifierError.context(e))?;

        Ok(Self {
            connection_id: msg
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_connection_id,
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
            signer: AccountId::from_str(msg.signer.as_str())
                .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

impl From<MsgConnectionOpenAck> for RawMsgConnectionOpenAck {
    fn from(ics_msg: MsgConnectionOpenAck) -> Self {
        RawMsgConnectionOpenAck {
            connection_id: ics_msg.connection_id.as_str().to_string(),
            counterparty_connection_id: ics_msg
                .counterparty_connection_id
                .map_or_else(|| "".to_string(), |v| v.as_str().to_string()),
            client_state: ics_msg
                .client_state
                .map_or_else(|| None, |v| Some(v.into())),
            proof_height: Some(ics_msg.proofs.height().into()),
            proof_try: ics_msg.proofs.object_proof().clone().into(),
            proof_client: ics_msg
                .proofs
                .client_proof()
                .clone()
                .map_or_else(Vec::new, |v| v.into()),
            proof_consensus: ics_msg
                .proofs
                .consensus_proof()
                .map_or_else(Vec::new, |v| v.proof().clone().into()),
            consensus_height: ics_msg
                .proofs
                .consensus_proof()
                .map_or_else(|| None, |h| Some(h.height().into())),
            version: ics_msg.version,
            signer: ics_msg.signer.to_string(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::test_utils::{get_dummy_account_id_raw, get_dummy_proof};
    use ibc_proto::ibc::core::client::v1::Height;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck;

    pub fn get_dummy_msg_conn_open_ack() -> RawMsgConnectionOpenAck {
        RawMsgConnectionOpenAck {
            connection_id: "srcconnection".to_string(),
            counterparty_connection_id: "tgtconnection".to_string(),
            proof_try: get_dummy_proof(),
            proof_height: Some(Height {
                version_number: 0,
                version_height: 10,
            }),
            proof_consensus: get_dummy_proof(),
            consensus_height: Some(Height {
                version_number: 0,
                version_height: 10,
            }),
            client_state: None,
            proof_client: vec![],
            version: "1.0.0".to_string(),
            signer: get_dummy_account_id_raw(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::core::client::v1::Height;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck;

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
                        version_number: 1,
                        version_height: 0,
                    }),
                    ..default_ack_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad consensus height, height is 0".to_string(),
                raw: RawMsgConnectionOpenAck {
                    consensus_height: Some(Height {
                        version_number: 1,
                        version_height: 0,
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
                "MsgConnOpenAck::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.raw,
                msg.err(),
            );
        }
    }

    #[test]
    fn to_and_from() {
        let raw = get_dummy_msg_conn_open_ack();
        let msg = MsgConnectionOpenAck::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgConnectionOpenAck::from(msg.clone());
        let msg_back = MsgConnectionOpenAck::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
