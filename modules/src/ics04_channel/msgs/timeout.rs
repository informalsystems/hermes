use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use tendermint::account::Id as AccountId;

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
