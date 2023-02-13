use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB,
};
use crate::base::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub trait HasTargetChainIds: HasBiRelayType {
    fn chain_id_a(&self) -> ChainIdA<Self>;

    fn chain_id_b(&self) -> ChainIdB<Self>;
}

pub trait HasTargetClientIds: HasBiRelayType {
    fn client_id_a(&self) -> ClientIdA<Self>;

    fn client_id_b(&self) -> ClientIdB<Self>;
}

#[async_trait]
pub trait CanBuildChainA: HasBiRelayType + HasErrorType {
    async fn build_chain_a(&self) -> Result<ChainA<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildChainB: HasBiRelayType + HasErrorType {
    async fn build_chain_b(&self) -> Result<ChainB<Self>, Self::Error>;
}

#[async_trait]
pub trait ChainABuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_chain_a(builder: &Builder) -> Result<ChainA<Builder>, Builder::Error>;
}

#[async_trait]
pub trait ChainBBuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_chain_b(builder: &Builder) -> Result<ChainB<Builder>, Builder::Error>;
}
