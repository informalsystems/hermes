use crate::base::one_for_all::traits::birelay::{OfaBiRelay, OfaBiRelayTypes};
use crate::base::one_for_all::traits::relay::OfaRelayTypes;
use crate::extra::one_for_all::traits::relay::{OfaFullRelay, OfaHomogeneousFullRelay};
use crate::extra::one_for_all::traits::runtime::OfaFullRuntime;

pub trait OfaFullBiRelayTypes:
    OfaBiRelayTypes<
    Runtime = Self::FullRuntime,
    RelayAToB = Self::FullRelayAToB,
    RelayBToA = Self::FullRelayBToA,
>
{
    type FullRuntime: OfaFullRuntime;

    type FullRelayAToB: OfaFullRelay<Preset = Self::Preset>;

    type FullRelayBToA: OfaFullRelay<
        Preset = Self::Preset,
        FullSrcChain = <Self::RelayAToB as OfaRelayTypes>::DstChain,
        FullDstChain = <Self::RelayAToB as OfaRelayTypes>::SrcChain,
        Error = <Self::RelayAToB as OfaRelayTypes>::Error,
    >;
}

impl<BiRelay> OfaFullBiRelayTypes for BiRelay
where
    BiRelay: OfaBiRelayTypes,
    BiRelay::Runtime: OfaFullRuntime,
    BiRelay::RelayAToB: OfaFullRelay,
    BiRelay::RelayBToA: OfaFullRelay<
        FullSrcChain = <BiRelay::RelayAToB as OfaRelayTypes>::DstChain,
        FullDstChain = <BiRelay::RelayAToB as OfaRelayTypes>::SrcChain,
    >,
{
    type FullRuntime = BiRelay::Runtime;

    type FullRelayAToB = BiRelay::RelayAToB;

    type FullRelayBToA = BiRelay::RelayBToA;
}

pub trait OfaFullBiRelay: OfaFullBiRelayTypes + OfaBiRelay {}

impl<BiRelay> OfaFullBiRelay for BiRelay where BiRelay: OfaFullBiRelayTypes + OfaBiRelay {}

pub trait OfaHomogeneousFullBiRelay:
    OfaFullBiRelayTypes<FullRelayAToB = Self::Relay, FullRelayBToA = Self::Relay>
{
    type Relay: OfaHomogeneousFullRelay;
}

impl<BiRelay, Relay> OfaHomogeneousFullBiRelay for BiRelay
where
    BiRelay: OfaFullBiRelayTypes<FullRelayAToB = Relay, FullRelayBToA = Relay>,
    Relay: OfaHomogeneousFullRelay,
{
    type Relay = Relay;
}
