use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::one_for_all::traits::birelay::OfaHomogeneousBiRelay;
use crate::one_for_all::traits::builder::{
    ChainACache, ChainBCache, OfaBuilderTypes, RelayAToBCache, RelayBToACache,
};
use crate::one_for_all::traits::runtime::OfaBaseRuntime;

pub struct OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    pub builder: Arc<Builder>,
    pub chain_a_cache: ChainACache<Builder>,
    pub chain_b_cache: ChainBCache<Builder>,
    pub relay_a_to_b_cache: RelayAToBCache<Builder>,
    pub relay_b_to_a_cache: RelayBToACache<Builder>,
}

impl<Builder> OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    pub fn new_with_heterogenous_cache(builder: Builder) -> Self {
        let chain_a_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let chain_b_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let relay_a_to_b_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let relay_b_to_a_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        Self {
            builder: Arc::new(builder),
            chain_a_cache,
            chain_b_cache,
            relay_a_to_b_cache,
            relay_b_to_a_cache,
        }
    }
}

impl<Builder> OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
    Builder::BiRelay: OfaHomogeneousBiRelay,
{
    pub fn new_with_homogenous_cache(builder: Builder) -> Self {
        let chain_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let relay_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        Self {
            builder: Arc::new(builder),
            chain_a_cache: chain_cache.clone(),
            chain_b_cache: chain_cache,
            relay_a_to_b_cache: relay_cache.clone(),
            relay_b_to_a_cache: relay_cache,
        }
    }
}

impl<Builder> Clone for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    fn clone(&self) -> Self {
        Self {
            builder: self.builder.clone(),
            chain_a_cache: self.chain_a_cache.clone(),
            chain_b_cache: self.chain_b_cache.clone(),
            relay_a_to_b_cache: self.relay_a_to_b_cache.clone(),
            relay_b_to_a_cache: self.relay_b_to_a_cache.clone(),
        }
    }
}
