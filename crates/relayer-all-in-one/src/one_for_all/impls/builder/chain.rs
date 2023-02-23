use async_trait::async_trait;

use crate::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::one_for_all::traits::builder::{ChainA, ChainB, ChainIdA, ChainIdB, OfaBuilder};
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;
use ibc_relayer_components::builder::impls::cache::BuildWithCache;
use ibc_relayer_components::builder::traits::chain::{CanBuildChain, ChainBuilder};
use ibc_relayer_components::builder::traits::target::chain::{ChainATarget, ChainBTarget};

pub struct BuildChainFromOfa;

#[async_trait]
impl<Builder> ChainBuilder<OfaBuilderWrapper<Builder>, ChainATarget> for BuildChainFromOfa
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain(
        builder: &OfaBuilderWrapper<Builder>,
        _target: ChainATarget,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_a(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> ChainBuilder<OfaBuilderWrapper<Builder>, ChainBTarget> for BuildChainFromOfa
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain(
        builder: &OfaBuilderWrapper<Builder>,
        _target: ChainBTarget,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_b(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> CanBuildChain<ChainATarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain(
        &self,
        target: ChainATarget,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Self::Error> {
        <BuildWithCache<BuildChainFromOfa>>::build_chain(self, target, chain_id).await
    }
}

#[async_trait]
impl<Builder> CanBuildChain<ChainBTarget> for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain(
        &self,
        target: ChainBTarget,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Self::Error> {
        <BuildWithCache<BuildChainFromOfa>>::build_chain(self, target, chain_id).await
    }
}
