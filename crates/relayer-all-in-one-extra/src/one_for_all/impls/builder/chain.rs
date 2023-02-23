use async_trait::async_trait;
use ibc_relayer_all_in_one::one_for_all::traits::birelay::OfaBiRelayPreset;
use ibc_relayer_all_in_one::one_for_all::traits::builder::{ChainA, ChainB, ChainIdA, ChainIdB};
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_components::builder::impls::cache::BuildWithCache;
use ibc_relayer_components::builder::traits::chain::{CanBuildChain, ChainBuilder};
use ibc_relayer_components::builder::traits::target::chain::{ChainATarget, ChainBTarget};

use crate::one_for_all::traits::builder::OfaFullBuilder;
use crate::one_for_all::types::builder::OfaFullBuilderWrapper;
use crate::std_prelude::*;

pub struct BuildChainFromOfa;

#[async_trait]
impl<Builder> ChainBuilder<OfaFullBuilderWrapper<Builder>, ChainATarget> for BuildChainFromOfa
where
    Builder: OfaFullBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain(
        builder: &OfaFullBuilderWrapper<Builder>,
        _target: ChainATarget,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_a(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> ChainBuilder<OfaFullBuilderWrapper<Builder>, ChainBTarget> for BuildChainFromOfa
where
    Builder: OfaFullBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_chain(
        builder: &OfaFullBuilderWrapper<Builder>,
        _target: ChainBTarget,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_b(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> CanBuildChain<ChainATarget> for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
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
impl<Builder> CanBuildChain<ChainBTarget> for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
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
