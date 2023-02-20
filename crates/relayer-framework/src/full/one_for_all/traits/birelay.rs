use crate::base::one_for_all::traits::birelay::{OfaBiRelay, OfaBiRelayTypes};
use crate::base::one_for_all::traits::relay::OfaRelayTypes;
use crate::full::one_for_all::traits::relay::{OfaFullRelay, OfaFullRelayTypes};
use crate::full::one_for_all::traits::runtime::OfaFullRuntime;

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
        FullSrcChain = <Self::RelayAToB as OfaFullRelayTypes>::FullDstChain,
        FullDstChain = <Self::RelayAToB as OfaFullRelayTypes>::FullSrcChain,
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
