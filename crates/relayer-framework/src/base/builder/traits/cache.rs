use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{
    ChainACache, ChainBCache, RelayAToBCache, RelayBToACache,
};
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;

pub trait HasChainACache: HasBiRelayType + HasRuntimeWithMutex {
    fn chain_a_cache(&self) -> &ChainACache<Self>;
}

pub trait HasChainBCache: HasBiRelayType + HasRuntimeWithMutex {
    fn chain_b_cache(&self) -> &ChainBCache<Self>;
}

pub trait HasRelayAToBCache: HasBiRelayType + HasRuntimeWithMutex {
    fn relay_a_to_b_cache(&self) -> &RelayAToBCache<Self>;
}

pub trait HasRelayBToACache: HasBiRelayType + HasRuntimeWithMutex {
    fn relay_b_to_a_cache(&self) -> &RelayBToACache<Self>;
}
