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

impl<BiRelay, RelayAToB, RelayBToA> AfoBaseBiRelay for BiRelay
where
    RelayAToB: AfoBaseRelay,
    RelayBToA: AfoBaseRelay<AfoSrcChain = RelayAToB::DstChain, AfoDstChain = RelayAToB::SrcChain>,
    BiRelay: HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
{
    type AfoRelayAToB = RelayAToB;

    type AfoRelayBToA = RelayBToA;
}
