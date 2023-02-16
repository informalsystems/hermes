use async_trait::async_trait;

use crate::base::builder::impls::cache::BuildWithCache;
use crate::base::builder::traits::chain::{
    CanBuildChainA, CanBuildChainB, ChainABuilder, ChainBBuilder,
};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{ChainA, ChainB, ChainIdA, ChainIdB, OfaBuilder};
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub struct BuildChainFromOfa;

#[async_trait]
impl<Builder> ChainABuilder<OfaBuilderWrapper<Builder>> for BuildChainFromOfa
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain_a(
        builder: &OfaBuilderWrapper<Builder>,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_a(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> ChainBBuilder<OfaBuilderWrapper<Builder>> for BuildChainFromOfa
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain_b(
        builder: &OfaBuilderWrapper<Builder>,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_b(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> CanBuildChainA for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain_a(
        &self,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Self::Error> {
        <BuildWithCache<BuildChainFromOfa>>::build_chain_a(self, chain_id).await
    }
}

#[async_trait]
impl<Builder> CanBuildChainB for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain_b(
        &self,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Self::Error> {
        <BuildWithCache<BuildChainFromOfa>>::build_chain_b(self, chain_id).await
    }
}
