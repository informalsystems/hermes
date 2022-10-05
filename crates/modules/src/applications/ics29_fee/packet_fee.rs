use core::str::FromStr;
use ibc_proto::cosmos::base::v1beta1::Coin as ProtoCoin;
use ibc_proto::ibc::applications::fee::v1::{
    Fee as ProtoFee, IdentifiedPacketFees as ProtoIdentifiedPacketFees, PacketFee as ProtoPacketFee,
};

use super::error::Error;
use crate::applications::transfer::amount::Amount;
use crate::applications::transfer::coin::RawCoin;
use crate::core::ics04_channel::packet_id::PacketId;
use crate::prelude::*;
use crate::signer::Signer;

/// The core type that encodes the different fees that are redeemable by relayers for relaying
/// different types of packets.
#[derive(Debug, Clone)]
pub struct Fee {
    /// The amount that the forward relayer redeems for submitting a recv packet.
    /// This fee is refunded to the payer in the case that the recv packet is not successfully relayed, i.e.,
    /// a timeout packet is relayed instead of the recv packet.
    pub recv_fee: Vec<RawCoin>,
    /// The amount that the reverse relayer redeems for relaying an acknowledgement packet.
    pub ack_fee: Vec<RawCoin>,
    /// The amount that the timeout relayer redeems for relaying a timeout packet.
    /// This fee is refunded to the payer in the case that a timeout packet is not relayed, i.e., a
    /// recv packet was successfully relayed instead.
    pub timeout_fee: Vec<RawCoin>,
}

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

impl TryFrom<ProtoFee> for Fee {
    type Error = Error;

    fn try_from(fee: ProtoFee) -> Result<Self, Error> {
        fn parse_coin_vec(coins: Vec<ProtoCoin>) -> Result<Vec<RawCoin>, Error> {
            coins
                .into_iter()
                .map(|coin| {
                    Ok(RawCoin {
                        denom: coin.denom,
                        amount: Amount::from_str(&coin.amount).map_err(Error::transfer)?,
                    })
                })
                .collect()
        }

        let recv_fee = parse_coin_vec(fee.recv_fee)?;
        let ack_fee = parse_coin_vec(fee.ack_fee)?;
        let timeout_fee = parse_coin_vec(fee.timeout_fee)?;

        Ok(Fee {
            recv_fee,
            ack_fee,
            timeout_fee,
        })
    }
}

impl TryFrom<ProtoPacketFee> for PacketFee {
    type Error = Error;

    fn try_from(packet_fee: ProtoPacketFee) -> Result<Self, Error> {
        let proto_fee = packet_fee.fee.ok_or_else(Error::empty_fee)?;

        let fee = Fee::try_from(proto_fee)?;

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
