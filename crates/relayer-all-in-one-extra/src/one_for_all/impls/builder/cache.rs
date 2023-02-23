use async_trait::async_trait;
use ibc_relayer_all_in_one::one_for_all::traits::birelay::OfaBiRelayPreset;
use ibc_relayer_all_in_one::one_for_all::traits::builder::RelayError;
use ibc_relayer_components::builder::traits::cache::{HasChainCache, HasRelayCache};
use ibc_relayer_components::builder::traits::target::chain::{ChainATarget, ChainBTarget};
use ibc_relayer_components::builder::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use ibc_relayer_components::builder::types::aliases::{
    ChainACache, ChainBCache, RelayAToBCache, RelayBToACache,
};
use ibc_relayer_components_extra::builder::traits::cache::HasBatchSenderCache;

use crate::one_for_all::traits::builder::{BatchSenderCacheA, BatchSenderCacheB, OfaFullBuilder};
use crate::one_for_all::types::builder::OfaFullBuilderWrapper;

#[async_trait]
impl<Build> HasChainCache<ChainATarget> for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    fn chain_cache(&self) -> &ChainACache<Self> {
        &self.chain_a_cache
    }
}

#[async_trait]
impl<Build> HasChainCache<ChainBTarget> for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    fn chain_cache(&self) -> &ChainBCache<Self> {
        &self.chain_b_cache
    }
}

#[async_trait]
impl<Build> HasRelayCache<RelayAToBTarget> for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    fn relay_cache(&self) -> &RelayAToBCache<Self> {
        &self.relay_a_to_b_cache
    }
}

#[async_trait]
impl<Build> HasRelayCache<RelayBToATarget> for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    fn relay_cache(&self) -> &RelayBToACache<Self> {
        &self.relay_b_to_a_cache
    }
}

#[async_trait]
impl<Build> HasBatchSenderCache<ChainATarget, RelayError<Build>> for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    fn batch_sender_cache(&self, _target: ChainATarget) -> &BatchSenderCacheA<Build> {
        &self.batch_sender_cache_a
    }
}

#[async_trait]
impl<Build> HasBatchSenderCache<ChainBTarget, RelayError<Build>> for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    fn batch_sender_cache(&self, _target: ChainBTarget) -> &BatchSenderCacheB<Build> {
        &self.batch_sender_cache_b
    }
}
