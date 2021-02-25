use std::convert::{TryFrom, TryInto};

use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgTimeoutOnClose as RawMsgTimeoutOnClose;

use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::{Packet, Sequence};
use crate::{proofs::Proofs, tx_msg::Msg};

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgTimeoutOnClose";

///
/// Message definition for packet timeout domain type.
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgTimeoutOnClose {
    pub packet: Packet,
    next_sequence_recv: Sequence,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgTimeoutOnClose {
    pub fn new(
        packet: Packet,
        next_sequence_recv: Sequence,
        proofs: Proofs,
        signer: AccountId,
    ) -> MsgTimeoutOnClose {
        Self {
            packet,
            next_sequence_recv,
            proofs,
            signer,
        }
    }
}

impl Msg for MsgTimeoutOnClose {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl Protobuf<RawMsgTimeoutOnClose> for MsgTimeoutOnClose {}

impl TryFrom<RawMsgTimeoutOnClose> for MsgTimeoutOnClose {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgTimeoutOnClose) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        let proofs = Proofs::new(
            raw_msg.proof_unreceived.into(),
            None,
            None,
            None,
            raw_msg
                .proof_height
                .ok_or(Kind::MissingHeight)?
                .try_into()
                .map_err(|e| Kind::InvalidProof.context(e))?,
        )
        .map_err(|e| Kind::InvalidProof.context(e))?;

        // TODO: Domain type verification for the next sequence: this should probably be > 0.

        Ok(MsgTimeoutOnClose {
            packet: raw_msg
                .packet
                .ok_or(Kind::MissingPacket)?
                .try_into()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            next_sequence_recv: Sequence::from(raw_msg.next_sequence_recv),
            signer,
            proofs,
        })
    }
}

impl From<MsgTimeoutOnClose> for RawMsgTimeoutOnClose {
    fn from(domain_msg: MsgTimeoutOnClose) -> Self {
        RawMsgTimeoutOnClose {
            packet: Some(domain_msg.packet.into()),
            proof_unreceived: domain_msg.proofs.object_proof().clone().into(),
            proof_close: domain_msg
                .proofs
                .other_proof
                .clone()
                .map_or_else(Vec::new, |v| v.into()),
            proof_height: Some(domain_msg.proofs.height().into()),
            next_sequence_recv: domain_msg.next_sequence_recv.into(),
            signer: account_to_string(domain_msg.signer).unwrap(),
        }
    }
}
