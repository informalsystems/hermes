use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::base::one_for_all::traits::builder::{
    ChainA, ChainB, ChainIdA, ChainIdB, OfaBuilderTypes, RelayAToB, RelayBToA,
};
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;

pub type Runtime<Builder> = <Builder as OfaBuilderTypes>::Runtime;

pub type Mutex<Builder, T> = <Runtime<Builder> as OfaBaseRuntime>::Mutex<T>;

pub type ChainACache<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdA<Builder>, ChainA<Builder>>>>;

pub type ChainBCache<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdB<Builder>, ChainB<Builder>>>>;

pub type RelayAToBCache<Builder> =
    Arc<Mutex<Builder, BTreeMap<(ChainIdA<Builder>, ChainIdB<Builder>), RelayAToB<Builder>>>>;

pub type RelayBToACache<Builder> =
    Arc<Mutex<Builder, BTreeMap<(ChainIdB<Builder>, ChainIdA<Builder>), RelayBToA<Builder>>>>;

pub struct OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    pub builder: Arc<Builder>,
    pub chain_a_cache: ChainACache<Builder>,
    pub chain_b_cache: ChainACache<Builder>,
    pub relay_a_to_b_cache: RelayAToBCache<Builder>,
    pub relay_b_to_a_cache: RelayBToACache<Builder>,
}

impl<Builder> OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilderTypes,
{
    pub fn new(
        builder: Builder,
        chain_a_cache: ChainACache<Builder>,
        chain_b_cache: ChainACache<Builder>,
        relay_a_to_b_cache: RelayAToBCache<Builder>,
        relay_b_to_a_cache: RelayBToACache<Builder>,
    ) -> Self {
        Self {
            builder: Arc::new(builder),
            chain_a_cache,
            chain_b_cache,
            relay_a_to_b_cache,
            relay_b_to_a_cache,
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
