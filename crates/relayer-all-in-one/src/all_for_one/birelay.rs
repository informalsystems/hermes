use ibc_relayer_components::logger::traits::level::HasLoggerWithBaseLevels;
use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;

use crate::all_for_one::relay::AfoRelay;
use crate::all_for_one::runtime::HasAfoRuntime;

pub trait AfoBiRelay:
    HasAfoRuntime
    + HasLoggerWithBaseLevels
    + CanAutoRelay
    + HasTwoWayRelay<RelayAToB = Self::AfoRelayAToB, RelayBToA = Self::AfoRelayBToA>
{
    type AfoRelayAToB: AfoRelay;

    type AfoRelayBToA: AfoRelay<
        AfoSrcChain = <Self::AfoRelayAToB as AfoRelay>::AfoDstChain,
        AfoDstChain = <Self::AfoRelayAToB as AfoRelay>::AfoSrcChain,
    >;
}

impl<BiRelay, RelayAToB, RelayBToA> AfoBiRelay for BiRelay
where
    RelayAToB: AfoRelay,
    RelayBToA: AfoRelay<AfoSrcChain = RelayAToB::AfoDstChain, AfoDstChain = RelayAToB::AfoSrcChain>,
    BiRelay: Clone
        + HasAfoRuntime
        + HasLoggerWithBaseLevels
        + CanAutoRelay
        + HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
{
    type AfoRelayAToB = RelayAToB;

    type AfoRelayBToA = RelayBToA;
}
