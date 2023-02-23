use crate::base::relay::traits::auto_relayer::CanAutoRelay;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::full::all_for_one::relay::AfoFullRelay;

pub trait AfoFullBiRelay:
    CanAutoRelay + HasTwoWayRelay<RelayAToB = Self::AfoRelayAToB, RelayBToA = Self::AfoRelayBToA>
{
    type AfoRelayAToB: AfoFullRelay;

    type AfoRelayBToA: AfoFullRelay<
        AfoSrcFullChain = <Self::AfoRelayAToB as AfoFullRelay>::AfoDstFullChain,
        AfoDstFullChain = <Self::AfoRelayAToB as AfoFullRelay>::AfoSrcFullChain,
    >;
}

impl<BiRelay, RelayAToB, RelayBToA> AfoFullBiRelay for BiRelay
where
    RelayAToB: AfoFullRelay,
    RelayBToA:
        AfoFullRelay<AfoSrcFullChain = RelayAToB::DstChain, AfoDstFullChain = RelayAToB::SrcChain>,
    BiRelay: CanAutoRelay + HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
{
    type AfoRelayAToB = RelayAToB;

    type AfoRelayBToA = RelayBToA;
}
