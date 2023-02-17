use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::chain::ChainBuildTarget;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{TargetChainCache, TargetRelayCache};
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;

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
