use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use tendermint::account::Id as AccountId;

/// Message type for `MsgPacket`.
const TYPE_MSG_PACKET: &str = "ics04/opaque";

///
/// Message definition for the packet wrapper domain type (`OpaquePacket` datagram).
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgPacket {
    packet: Packet,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgPacket {
    pub fn new(
        packet: Packet,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgPacket, Error> {
        Ok(Self {
            packet: packet
                .validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            proofs: Proofs::new(proof, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }

    // returns the base64-encoded bytes used for the
    // data field when signing the packet
    pub fn get_data_bytes() -> Vec<u8> {
        todo!()
    }
}

impl Msg for MsgPacket {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_PACKET.to_string()
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
