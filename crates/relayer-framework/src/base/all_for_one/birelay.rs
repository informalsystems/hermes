use crate::base::all_for_one::chain::AfoBaseChain;
use crate::base::all_for_one::relay::AfoBaseRelay;
use crate::base::relay::traits::two_way::HasTwoWayRelay;

pub trait AfoBaseBiRelay:
    HasTwoWayRelay<RelayAToB = Self::AfoRelayAToB, RelayBToA = Self::AfoRelayBToA>
{
    type AfoRelayAToB: AfoBaseRelay;

    type AfoRelayBToA: AfoBaseRelay<
        AfoSrcChain = <Self::AfoRelayAToB as AfoBaseRelay>::AfoDstChain,
        AfoDstChain = <Self::AfoRelayAToB as AfoBaseRelay>::AfoSrcChain,
    >;
}

impl<BiRelay, ChainA, ChainB, RelayAToB, RelayBToA, PacketAToB, PacketBToA> AfoBaseBiRelay
    for BiRelay
where
    ChainA: AfoBaseChain<ChainB, IncomingPacket = PacketBToA, OutgoingPacket = PacketAToB>,
    ChainB: AfoBaseChain<ChainA, IncomingPacket = PacketAToB, OutgoingPacket = PacketBToA>,
    RelayAToB: AfoBaseRelay<AfoSrcChain = ChainA, AfoDstChain = ChainB>,
    RelayBToA: AfoBaseRelay<AfoSrcChain = ChainB, AfoDstChain = ChainA>,
    BiRelay: HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
{
    type AfoRelayAToB = RelayAToB;

    type AfoRelayBToA = RelayBToA;
}
