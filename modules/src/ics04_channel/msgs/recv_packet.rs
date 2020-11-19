use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::{proofs::Proofs, tx_msg::Msg, Height};

use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as RawMsgRecvPacket;
use std::convert::{TryFrom, TryInto};
use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

/// Message type for `MsgPacket`.
const TYPE_MSG_PACKET: &str = "ics04/opaque";

///
/// Message definition for the packet wrapper domain type (`OpaquePacket` datagram).
/// This whole module is WIP: https://github.com/informalsystems/ibc-rs/issues/95.
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgRecvPacket {
    packet: Packet,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgRecvPacket {
    pub fn new(
        packet: Packet,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgRecvPacket, Error> {
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

impl Msg for MsgRecvPacket {
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

impl Protobuf<RawMsgRecvPacket> for MsgRecvPacket {}

impl TryFrom<RawMsgRecvPacket> for MsgRecvPacket {
    type Error = anomaly::Error<Kind>;

    // This depends on Packet domain type (not implemented yet).
    #[allow(unreachable_code, unused_variables)]
    fn try_from(raw_msg: RawMsgRecvPacket) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        let proofs = Proofs::new(
            raw_msg.proof.into(),
            None,
            None,
            raw_msg
                .proof_height
                .ok_or_else(|| Kind::MissingHeight)?
                .try_into()
                .map_err(|e| Kind::InvalidProof.context(e))?,
        )
        .map_err(|e| Kind::InvalidProof.context(e))?;

        Ok(MsgRecvPacket {
            packet: todo!(),
            proofs,
            signer,
        })
    }
}

impl From<MsgRecvPacket> for RawMsgRecvPacket {
    fn from(domain_msg: MsgRecvPacket) -> Self {
        RawMsgRecvPacket {
            packet: None, // TODO: Should be: `Some(domain_msg.packet.into())`.
            proof: domain_msg.proofs.object_proof().clone().into(),
            proof_height: Some(domain_msg.proofs.height().into()),
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}
