use async_trait::async_trait;

use crate::base::builder::traits::cache::{
    HasChainACache, HasChainBCache, HasRelayAToBCache, HasRelayBToACache,
};
use crate::base::builder::types::aliases::{
    ChainACache, ChainBCache, RelayAToBCache, RelayBToACache,
};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::OfaBuilder;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;

#[async_trait]
impl<Builder> HasChainACache for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    fn chain_a_cache(&self) -> &ChainACache<Self> {
        self.builder.chain_a_cache()
    }
}

#[async_trait]
impl<Builder> HasChainBCache for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    fn chain_b_cache(&self) -> &ChainBCache<Self> {
        self.builder.chain_b_cache()
    }
}

#[async_trait]
impl<Builder> HasRelayAToBCache for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    fn relay_a_to_b_cache(&self) -> &RelayAToBCache<Self> {
        self.builder.relay_a_to_b_cache()
    }
}

#[async_trait]
impl<Builder> HasRelayBToACache for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    fn relay_b_to_a_cache(&self) -> &RelayBToACache<Self> {
        self.builder.relay_b_to_a_cache()
    }
}
