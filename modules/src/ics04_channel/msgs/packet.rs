use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::address::{account_to_string, string_to_account};
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as RawMsgPacket;
use tendermint::account::Id as AccountId;
use tendermint_proto::DomainType;
use std::convert::TryFrom;

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

impl DomainType<RawMsgPacket> for MsgPacket {}

#[allow(unreachable_code, unused_variables)]
impl TryFrom<RawMsgPacket> for MsgPacket {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgPacket) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        Ok(MsgPacket {
            packet: Packet,
            proofs: todo!(),
            signer,
        })
    }
}

impl From<MsgPacket> for RawMsgPacket {
    fn from(domain_msg: MsgPacket) -> Self {
        RawMsgPacket {
            packet: None,
            proof: vec![],
            proof_height: None,
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}