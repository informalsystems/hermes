use crate::build::traits::birelay::HasBiRelayType;
use crate::build::traits::target::chain::ChainBuildTarget;
use crate::build::traits::target::relay::RelayBuildTarget;
use crate::build::types::aliases::{TargetChainCache, TargetRelayCache};
use crate::runtime::traits::mutex::HasRuntimeWithMutex;

pub trait HasChainCache<Target>: HasBiRelayType + HasRuntimeWithMutex
where
    Target: ChainBuildTarget<Self>,
{
    fn chain_cache(&self) -> &TargetChainCache<Self, Target>;
}

pub trait HasRelayCache<Target>: HasBiRelayType + HasRuntimeWithMutex
where
    Target: RelayBuildTarget<Self>,
{
    fn relay_cache(&self) -> &TargetRelayCache<Self, Target>;
}
