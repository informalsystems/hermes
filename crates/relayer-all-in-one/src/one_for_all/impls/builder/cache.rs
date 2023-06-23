use async_trait::async_trait;
use ibc_relayer_components::builder::traits::cache::{HasChainCache, HasRelayCache};
use ibc_relayer_components::builder::traits::target::chain::{ChainATarget, ChainBTarget};
use ibc_relayer_components::builder::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use ibc_relayer_components::builder::types::aliases::{
    ChainACache, ChainBCache, RelayAToBCache, RelayBToACache,
};

use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::builder::OfaBuilderWrapper;

#[async_trait]
impl<Builder> HasChainCache<ChainATarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    fn chain_cache(&self) -> &ChainACache<Self> {
        &self.chain_a_cache
    }
}

#[async_trait]
impl<Builder> HasChainCache<ChainBTarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    fn chain_cache(&self) -> &ChainBCache<Self> {
        &self.chain_b_cache
    }
}

#[async_trait]
impl<Builder> HasRelayCache<RelayAToBTarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    fn relay_cache(&self) -> &RelayAToBCache<Self> {
        &self.relay_a_to_b_cache
    }
}

#[async_trait]
impl<Builder> HasRelayCache<RelayBToATarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    fn relay_cache(&self) -> &RelayBToACache<Self> {
        &self.relay_b_to_a_cache
    }
}
