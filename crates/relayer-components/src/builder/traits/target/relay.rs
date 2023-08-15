use crate::builder::traits::birelay::types::HasBiRelayType;
use crate::builder::traits::target::chain::{ChainATarget, ChainBTarget, ChainBuildTarget};
use crate::builder::types::aliases::{RelayAToB, RelayBToA, RelayError};
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;

#[derive(Default)]
pub struct RelayAToBTarget;

#[derive(Default)]
pub struct RelayBToATarget;

pub trait RelayBuildTarget<Build>: Default + Async
where
    Build: HasBiRelayType,
{
    type TargetRelay: HasRelayChains<Error = RelayError<Build>>;

    type SrcChainTarget: ChainBuildTarget<
        Build,
        TargetChain = <Self::TargetRelay as HasRelayChains>::SrcChain,
        CounterpartyChain = <Self::TargetRelay as HasRelayChains>::DstChain,
    >;

    type DstChainTarget: ChainBuildTarget<
        Build,
        TargetChain = <Self::TargetRelay as HasRelayChains>::DstChain,
        CounterpartyChain = <Self::TargetRelay as HasRelayChains>::SrcChain,
    >;
}

impl<Build> RelayBuildTarget<Build> for RelayAToBTarget
where
    Build: HasBiRelayType,
{
    type TargetRelay = RelayAToB<Build>;

    type SrcChainTarget = ChainATarget;

    type DstChainTarget = ChainBTarget;
}

impl<Build> RelayBuildTarget<Build> for RelayBToATarget
where
    Build: HasBiRelayType,
{
    type TargetRelay = RelayBToA<Build>;

    type SrcChainTarget = ChainBTarget;

    type DstChainTarget = ChainATarget;
}
