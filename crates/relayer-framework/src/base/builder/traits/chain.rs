use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{ChainA, ChainB};
use crate::base::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildChainA: HasBiRelayType + HasErrorType {
    async fn build_chain_a(&self) -> Result<ChainA<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildChainB: HasBiRelayType + HasErrorType {
    async fn build_chain_b(&self) -> Result<ChainB<Self>, Self::Error>;
}
