use crate::base::traits::birelay::CosmosBiRelay;
use crate::base::traits::relay::CosmosRelay;
use crate::full::traits::relay::{CosmosFullRelay, CosmosHomogenousFullRelay};

pub trait CosmosFullBiRelay:
    CosmosBiRelay<RelayAToB = Self::FullRelayAToB, RelayBToA = Self::FullRelayBToA>
{
    type FullRelayAToB: CosmosFullRelay<Preset = Self::Preset>;

    type FullRelayBToA: CosmosFullRelay<
        Preset = Self::Preset,
        FullSrcChain = <Self::RelayAToB as CosmosRelay>::DstChain,
        FullDstChain = <Self::RelayAToB as CosmosRelay>::SrcChain,
    >;
}

impl<BiRelay> CosmosFullBiRelay for BiRelay
where
    BiRelay: CosmosBiRelay,
    BiRelay::RelayAToB: CosmosFullRelay<Preset = BiRelay::Preset>,
    BiRelay::RelayBToA: CosmosFullRelay<
        Preset = BiRelay::Preset,
        FullSrcChain = <BiRelay::RelayAToB as CosmosRelay>::DstChain,
        FullDstChain = <BiRelay::RelayAToB as CosmosRelay>::SrcChain,
    >,
{
    type FullRelayAToB = BiRelay::RelayAToB;

    type FullRelayBToA = BiRelay::RelayBToA;
}

pub trait CosmosHomogenousFullBiRelay:
    CosmosFullBiRelay<FullRelayAToB = Self::FullRelay, FullRelayBToA = Self::FullRelay>
{
    type FullRelay: CosmosHomogenousFullRelay<Preset = Self::Preset>;
}

impl<BiRelay, Relay> CosmosHomogenousFullBiRelay for BiRelay
where
    BiRelay: CosmosFullBiRelay<FullRelayAToB = Relay, FullRelayBToA = Relay>,
    Relay: CosmosHomogenousFullRelay<Preset = Self::Preset>,
{
    type FullRelay = Relay;
}
