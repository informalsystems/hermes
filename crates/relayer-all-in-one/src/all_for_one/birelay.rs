use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;

use crate::all_for_one::relay::AfoBaseRelay;

pub trait AfoBaseBiRelay:
    CanAutoRelay + HasTwoWayRelay<RelayAToB = Self::AfoRelayAToB, RelayBToA = Self::AfoRelayBToA>
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
    BiRelay: CanAutoRelay + HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
{
    type AfoRelayAToB = RelayAToB;

    type AfoRelayBToA = RelayBToA;
}
