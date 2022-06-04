use core::str::FromStr;
use ibc_proto::ibc::applications::fee::v1::Fee;
use ibc_proto::ibc::applications::fee::v1::{
    IdentifiedPacketFees as ProtoIdentifiedPacketFees, PacketFee as ProtoPacketFee,
};

use super::error::Error;
use crate::core::ics04_channel::packet_id::PacketId;
use crate::prelude::*;
use crate::signer::Signer;

#[derive(Debug, Clone)]
pub struct PacketFee {
    pub fee: Fee,
    pub refund_address: Signer,
    // do not expose relayer field as it is currently a reserved field
}

#[derive(Debug, Clone)]
pub struct IdentifiedPacketFees {
    pub packet_id: PacketId,
    pub packet_fees: Vec<PacketFee>,
}

impl TryFrom<ProtoPacketFee> for PacketFee {
    type Error = Error;

    fn try_from(packet_fee: ProtoPacketFee) -> Result<Self, Error> {
        let fee = packet_fee.fee.ok_or_else(Error::empty_fee)?;

        let refund_address = Signer::from_str(&packet_fee.refund_address).map_err(Error::signer)?;

        Ok(PacketFee {
            fee,
            refund_address,
        })
    }
}

impl TryFrom<ProtoIdentifiedPacketFees> for IdentifiedPacketFees {
    type Error = Error;

    fn try_from(fees: ProtoIdentifiedPacketFees) -> Result<Self, Error> {
        let raw_packet_id = fees.packet_id.ok_or_else(Error::empty_packet_id)?;

        let packet_id = PacketId::try_from(raw_packet_id).map_err(Error::channel)?;

        let packet_fees = fees
            .packet_fees
            .into_iter()
            .map(PacketFee::try_from)
            .collect::<Result<_, _>>()?;

        Ok(IdentifiedPacketFees {
            packet_id,
            packet_fees,
        })
    }
}
