use crate::base::chain::traits::types::packet::HasIbcPacketTypes;
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;

pub trait HasTwoWayRelay: HasErrorType {
    type ChainA: HasIbcPacketTypes<
        Self::ChainB,
        IncomingPacket = Self::PacketBToA,
        OutgoingPacket = Self::PacketAToB,
    >;

    type ChainB: HasIbcPacketTypes<
        Self::ChainA,
        IncomingPacket = Self::PacketAToB,
        OutgoingPacket = Self::PacketBToA,
    >;

    type PacketAToB: Async;

    type PacketBToA: Async;

    type RelayAToB: HasRelayTypes<
        SrcChain = Self::ChainA,
        DstChain = Self::ChainB,
        Packet = Self::PacketAToB,
        Error = Self::Error,
    >;

    type RelayBToA: HasRelayTypes<
        SrcChain = Self::ChainB,
        DstChain = Self::ChainA,
        Packet = Self::PacketBToA,
        Error = Self::Error,
    >;

    fn relay_a_to_b(&self) -> &Self::RelayAToB;

    fn relay_b_to_a(&self) -> &Self::RelayBToA;
}
