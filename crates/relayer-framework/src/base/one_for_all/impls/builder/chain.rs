use async_trait::async_trait;

use crate::base::builder::traits::chain::{ChainABuilder, ChainBBuilder};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{ChainA, ChainB, OfaBuilder};
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
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_a().await?;

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
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_b().await?;

        Ok(OfaChainWrapper::new(chain))
    }
}
