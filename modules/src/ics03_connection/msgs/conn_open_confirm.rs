use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
use tendermint_proto::Protobuf;

use tendermint::account::Id as AccountId;

use crate::address::{account_to_string, string_to_account};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics24_host::identifier::ConnectionId;
use crate::{proofs::Proofs, tx_msg::Msg};

pub const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenConfirm";

///
/// Message definition for `MsgConnectionOpenConfirm` (i.e., `ConnOpenConfirm` datagram).
///
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgConnectionOpenConfirm {
    pub connection_id: ConnectionId,
    pub proofs: Proofs,
    pub signer: AccountId,
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

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgConnectionOpenConfirm> for MsgConnectionOpenConfirm {}

impl TryFrom<RawMsgConnectionOpenConfirm> for MsgConnectionOpenConfirm {
    type Error = anomaly::Error<Kind>;

    fn try_from(msg: RawMsgConnectionOpenConfirm) -> Result<Self, Self::Error> {
        let signer = string_to_account(msg.signer).map_err(|e| Kind::InvalidAddress.context(e))?;

        let proof_height = msg
            .proof_height
            .ok_or(Kind::MissingProofHeight)?
            .try_into() // Cast from the raw height type into the domain type.
            .map_err(|e| Kind::InvalidProof.context(e))?;
        Ok(Self {
            connection_id: msg
                .connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proofs: Proofs::new(msg.proof_ack.into(), None, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl From<MsgConnectionOpenConfirm> for RawMsgConnectionOpenConfirm {
    fn from(ics_msg: MsgConnectionOpenConfirm) -> Self {
        RawMsgConnectionOpenConfirm {
            connection_id: ics_msg.connection_id.as_str().to_string(),
            proof_ack: ics_msg.proofs.object_proof().clone().into(),
            proof_height: Some(ics_msg.proofs.height().into()),
            signer: account_to_string(ics_msg.signer).unwrap(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::client::v1::Height;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;

    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    pub fn get_dummy_msg_conn_open_confirm() -> RawMsgConnectionOpenConfirm {
        RawMsgConnectionOpenConfirm {
            connection_id: "srcconnection".to_string(),
            proof_ack: get_dummy_proof(),
            proof_height: Some(Height {
                revision_number: 0,
                revision_height: 10,
            }),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use ibc_proto::ibc::core::client::v1::Height;
    use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;

    use crate::ics03_connection::msgs::conn_open_confirm::test_util::get_dummy_msg_conn_open_confirm;
    use crate::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;

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
                        revision_number: 1,
                        revision_height: 0,
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

    #[test]
    fn to_and_from() {
        let raw = get_dummy_msg_conn_open_confirm();
        let msg = MsgConnectionOpenConfirm::try_from(raw.clone()).unwrap();
        let raw_back = RawMsgConnectionOpenConfirm::from(msg.clone());
        let msg_back = MsgConnectionOpenConfirm::try_from(raw_back.clone()).unwrap();
        assert_eq!(raw, raw_back);
        assert_eq!(msg, msg_back);
    }
}
