use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use ibc_proto::ibc::core::channel::v1::MsgTimeout as RawMsgTimeout;
use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use std::convert::TryFrom;

/// Message type for the `MsgTimeout` message.
const TYPE_MSG_TIMEOUT: &str = "ics04/timeout";

///
/// Message definition for packet timeout domain type.
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgTimeout {
    packet: Packet,
    next_sequence_recv: Option<u64>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgTimeout {
    pub fn new(
        packet: Packet,
        next_sequence_recv: Option<u64>,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgTimeout, Error> {
        Ok(Self {
            packet: packet
                .validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            next_sequence_recv,
            proofs: Proofs::new(proof, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgTimeout {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_TIMEOUT.to_string()
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

impl Protobuf<RawMsgTimeout> for MsgTimeout {}

#[allow(unreachable_code, unused_variables)]
impl TryFrom<RawMsgTimeout> for MsgTimeout {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgTimeout) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        Ok(MsgTimeout {
            packet: todo!(),
            next_sequence_recv: None,
            signer,
            proofs: todo!(),
        })
    }
}

impl From<MsgTimeout> for RawMsgTimeout {
    fn from(domain_msg: MsgTimeout) -> Self {
        RawMsgTimeout {
            packet: None,
            proof: vec![],
            proof_height: None,
            next_sequence_recv: 0,
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}
