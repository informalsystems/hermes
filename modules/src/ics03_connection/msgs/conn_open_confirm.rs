use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::str::{from_utf8, FromStr};

use ibc_proto::ibc::connection::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
use tendermint::account::Id as AccountId;

use crate::ics03_connection::error::{Error, Kind};
use crate::ics24_host::identifier::ConnectionId;
use crate::proofs::Proofs;
use crate::tx_msg::Msg;

/// Message type for the `MsgConnectionOpenConfirm` message.
pub const TYPE_MSG_CONNECTION_OPEN_CONFIRM: &str = "connection_open_confirm";

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
    use ibc_proto::ibc::client::Height;
    use ibc_proto::ibc::connection::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;

    use crate::ics03_connection::msgs::test_util::{get_dummy_account_id_bytes, get_dummy_proof};

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
    use ibc_proto::ibc::connection::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;

    use crate::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
    use crate::ics03_connection::msgs::test_util::get_dummy_msg_conn_open_confirm;

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
