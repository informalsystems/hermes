use crate::base::chain::traits::types::packet::HasIbcPacketTypes;
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::relay::traits::types::HasRelayTypes;
use core::fmt::Debug;

#[derive(Clone)]
pub struct TwoWayRelayContext<RelayAToB, RelayBToA> {
    pub relay_a_to_b: RelayAToB,
    pub relay_b_to_a: RelayBToA,
}

impl<Error, RelayAToB, RelayBToA> HasErrorType for TwoWayRelayContext<RelayAToB, RelayBToA>
where
    Error: Debug + Async,
    RelayAToB: HasRelayTypes<Error = Error>,
    RelayBToA: HasRelayTypes<Error = Error>,
{
    type Error = Error;
}

impl<Error, ChainA, ChainB, RelayAToB, RelayBToA, PacketAToB, PacketBToA> HasTwoWayRelay
    for TwoWayRelayContext<RelayAToB, RelayBToA>
where
    Error: Debug + Async,
    PacketAToB: Async,
    PacketBToA: Async,
    ChainA: HasIbcPacketTypes<ChainB, IncomingPacket = PacketBToA, OutgoingPacket = PacketAToB>,
    ChainB: HasIbcPacketTypes<ChainA, IncomingPacket = PacketAToB, OutgoingPacket = PacketBToA>,
    RelayAToB:
        HasRelayTypes<SrcChain = ChainA, DstChain = ChainB, Packet = PacketAToB, Error = Error>,
    RelayBToA:
        HasRelayTypes<SrcChain = ChainB, DstChain = ChainA, Packet = PacketBToA, Error = Error>,
{
    type ChainA = ChainA;

    type ChainB = ChainB;

    type PacketAToB = PacketAToB;

    type PacketBToA = PacketBToA;

    type RelayAToB = RelayAToB;

    type RelayBToA = RelayBToA;

    fn relay_a_to_b(&self) -> &RelayAToB {
        &self.relay_a_to_b
    }

    fn relay_b_to_a(&self) -> &RelayBToA {
        &self.relay_b_to_a
    }
}
