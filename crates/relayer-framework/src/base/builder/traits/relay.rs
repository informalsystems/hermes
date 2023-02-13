use async_trait::async_trait;

use crate::base::builder::types::aliases::{ChainA, ChainB, RelayAToB, RelayBToA};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

use super::birelay::HasBiRelayType;

#[async_trait]
pub trait CanBuildRelayAToB: HasBiRelayType + HasErrorType {
    async fn build_relay_a_to_b(&self) -> Result<RelayAToB<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayBToA: HasBiRelayType + HasErrorType {
    async fn build_relay_b_to_a(&self) -> Result<RelayBToA<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayAToBFromChains: HasBiRelayType + HasErrorType {
    async fn build_relay_a_to_b_from_chains(
        &self,
        chain_a: ChainA<Self>,
        chain_b: ChainB<Self>,
    ) -> Result<RelayAToB<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayBToAFromChains: HasBiRelayType + HasErrorType {
    async fn build_relay_b_to_a_from_chains(
        &self,
        chain_b: ChainB<Self>,
        chain_a: ChainA<Self>,
    ) -> Result<RelayBToA<Self>, Self::Error>;
}

#[async_trait]
pub trait RelayAToBBuilder<Builder>: Async
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_relay_a_to_b(builder: &Builder) -> Result<RelayAToB<Builder>, Builder::Error>;
}

#[async_trait]
pub trait RelayBToABuilder<Builder>: Async
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_relay_b_to_a(builder: &Builder) -> Result<RelayBToA<Builder>, Builder::Error>;
}
