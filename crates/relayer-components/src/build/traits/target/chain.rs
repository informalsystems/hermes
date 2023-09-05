use crate::build::traits::birelay::HasBiRelayType;
use crate::build::types::aliases::{ChainA, ChainB};
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

#[derive(Default)]
pub struct ChainATarget;

#[derive(Default)]
pub struct ChainBTarget;

pub trait ChainBuildTarget<Build>: Default + Async {
    type TargetChain: HasIbcChainTypes<Self::CounterpartyChain>;

    type CounterpartyChain: HasIbcChainTypes<Self::TargetChain>;
}

impl<Build> ChainBuildTarget<Build> for ChainATarget
where
    Build: HasBiRelayType,
{
    type TargetChain = ChainA<Build>;

    type CounterpartyChain = ChainB<Build>;
}

impl<Build> ChainBuildTarget<Build> for ChainBTarget
where
    Build: HasBiRelayType,
{
    type TargetChain = ChainB<Build>;

    type CounterpartyChain = ChainA<Build>;
}
