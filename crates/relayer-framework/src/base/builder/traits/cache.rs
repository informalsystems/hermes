use crate::base::builder::traits::target::chain::HasChainBuildTarget;
use crate::base::builder::traits::target::relay::HasRelayBuildTarget;
use crate::base::builder::types::aliases::{RelayAToBCache, TargetChainCache};
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;

pub trait HasChainCache<Target>: HasChainBuildTarget<Target> + HasRuntimeWithMutex {
    fn chain_cache(&self) -> &TargetChainCache<Self, Target>;
}

pub trait HasRelayCache<Target>: HasRelayBuildTarget<Target> + HasRuntimeWithMutex {
    fn relay_cache(&self) -> &RelayAToBCache<Self>;
}
