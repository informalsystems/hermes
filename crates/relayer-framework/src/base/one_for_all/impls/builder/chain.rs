use async_trait::async_trait;

use crate::base::builder::traits::builder::TargetBuilder;
use crate::base::one_for_all::traits::builder::OfaBuilder;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
use crate::std_prelude::*;

pub struct BuildChainAFromOfa;

pub struct BuildChainBFromOfa;

#[async_trait]
impl<Builder> TargetBuilder<OfaBuilderWrapper<Builder>, Builder::ChainA> for BuildChainAFromOfa
where
    Builder: OfaBuilder,
{
    async fn build_target(
        builder: &OfaBuilderWrapper<Builder>,
    ) -> Result<Builder::ChainA, Builder::Error> {
        builder.builder.build_chain_a().await
    }
}

#[async_trait]
impl<Builder> TargetBuilder<OfaBuilderWrapper<Builder>, Builder::ChainB> for BuildChainBFromOfa
where
    Builder: OfaBuilder,
{
    async fn build_target(
        builder: &OfaBuilderWrapper<Builder>,
    ) -> Result<Builder::ChainB, Builder::Error> {
        builder.builder.build_chain_b().await
    }
}
