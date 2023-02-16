use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{ChainA, ChainB, ChainIdA, ChainIdB};
use crate::base::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildChainA: HasBiRelayType + HasErrorType {
    async fn build_chain_a(&self, chain_id: &ChainIdA<Self>) -> Result<ChainA<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildChainB: HasBiRelayType + HasErrorType {
    async fn build_chain_b(&self, chain_id: &ChainIdB<Self>) -> Result<ChainB<Self>, Self::Error>;
}

#[async_trait]
pub trait ChainABuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_chain_a(
        builder: &Builder,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<ChainA<Builder>, Builder::Error>;
}

#[async_trait]
pub trait ChainBBuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_chain_b(
        builder: &Builder,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<ChainB<Builder>, Builder::Error>;
}
