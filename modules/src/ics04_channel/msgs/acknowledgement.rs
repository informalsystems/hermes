use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use ibc_proto::ibc::core::channel::v1::MsgAcknowledgement as RawMsgAcknowledgement;
use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use std::convert::TryFrom;

/// Message type for the `MsgAcknowledgement` message.
const TYPE_MSG_ACKNOWLEDGEMENT: &str = "ics04/opaque";

///
/// Message definition for packet acknowledgements.
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgAcknowledgement {
    packet: Packet,
    acknowledgement: Vec<u8>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgAcknowledgement {
    pub fn new(
        packet: Packet,
        acknowledgement: Vec<u8>,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgAcknowledgement, Error> {
        if acknowledgement.len() > 100 {
            return Err(Kind::AcknowledgementTooLong.into());
        }

        Ok(Self {
            packet: packet
                .validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            acknowledgement,
            proofs: Proofs::new(proof, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgAcknowledgement {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_ACKNOWLEDGEMENT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl Protobuf<RawMsgAcknowledgement> for MsgAcknowledgement {}

#[allow(unreachable_code)]
impl TryFrom<RawMsgAcknowledgement> for MsgAcknowledgement {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgAcknowledgement) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        Ok(MsgAcknowledgement {
            packet: Packet,
            acknowledgement: vec![],
            signer,
            proofs: todo!(),
        })
    }
}

impl From<MsgAcknowledgement> for RawMsgAcknowledgement {
    fn from(domain_msg: MsgAcknowledgement) -> Self {
        RawMsgAcknowledgement {
            packet: None,
            acknowledgement: vec![],
            proof: vec![],
            signer: account_to_string(domain_msg.signer).unwrap(),
            proof_height: None,
        }
    }
}
