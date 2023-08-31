use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;

use crate::one_for_all::traits::birelay::OfaHomogeneousBiRelay;
use crate::one_for_all::traits::builder::{
    BatchSenderCacheA, BatchSenderCacheB, ChainACache, ChainBCache, OfaBuilder, RelayAToBCache,
    RelayBToACache,
};

pub struct OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    pub builder: Arc<Build>,
    pub chain_a_cache: ChainACache<Build>,
    pub chain_b_cache: ChainBCache<Build>,
    pub relay_a_to_b_cache: RelayAToBCache<Build>,
    pub relay_b_to_a_cache: RelayBToACache<Build>,
    pub batch_sender_cache_a: Arc<BatchSenderCacheA<Build>>,
    pub batch_sender_cache_b: Arc<BatchSenderCacheB<Build>>,
}

impl<Builder> OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    pub fn new_with_heterogenous_cache(builder: Builder) -> Self {
        let chain_a_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let chain_b_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let relay_a_to_b_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let relay_b_to_a_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let batch_sender_cache_a = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let batch_sender_cache_b = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        Self {
            builder: Arc::new(builder),
            chain_a_cache,
            chain_b_cache,
            relay_a_to_b_cache,
            relay_b_to_a_cache,
            batch_sender_cache_a,
            batch_sender_cache_b,
        }
    }
}

impl<Builder> OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::BiRelay: OfaHomogeneousBiRelay,
{
    pub fn new_with_homogenous_cache(builder: Builder) -> Self {
        let chain_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let relay_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        let batch_sender_cache = Arc::new(Builder::Runtime::new_mutex(BTreeMap::new()));

        Self {
            builder: Arc::new(builder),
            chain_a_cache: chain_cache.clone(),
            chain_b_cache: chain_cache,
            relay_a_to_b_cache: relay_cache.clone(),
            relay_b_to_a_cache: relay_cache,
            batch_sender_cache_a: batch_sender_cache.clone(),
            batch_sender_cache_b: batch_sender_cache,
        }
    }
}

impl<Builder> Clone for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    fn clone(&self) -> Self {
        Self {
            builder: self.builder.clone(),
            chain_a_cache: self.chain_a_cache.clone(),
            chain_b_cache: self.chain_b_cache.clone(),
            relay_a_to_b_cache: self.relay_a_to_b_cache.clone(),
            relay_b_to_a_cache: self.relay_b_to_a_cache.clone(),
            batch_sender_cache_a: self.batch_sender_cache_a.clone(),
            batch_sender_cache_b: self.batch_sender_cache_b.clone(),
        }
    }
}
