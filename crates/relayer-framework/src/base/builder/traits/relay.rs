use async_trait::async_trait;

use crate::base::builder::types::aliases::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

use super::birelay::HasBiRelayType;

#[async_trait]
pub trait CanBuildRelayAToB: HasBiRelayType + HasErrorType {
    async fn build_relay_a_to_b(
        &self,
        src_chain_id: &ChainIdA<Self>,
        dst_chain_id: &ChainIdB<Self>,
        src_client_id: &ClientIdA<Self>,
        dst_client_id: &ClientIdB<Self>,
    ) -> Result<RelayAToB<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayBToA: HasBiRelayType + HasErrorType {
    async fn build_relay_b_to_a(
        &self,
        src_chain_id: &ChainIdB<Self>,
        dst_chain_id: &ChainIdA<Self>,
        src_client_id: &ClientIdB<Self>,
        dst_client_id: &ClientIdA<Self>,
    ) -> Result<RelayBToA<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayAToBFromChains: HasBiRelayType + HasErrorType {
    async fn build_relay_a_to_b_from_chains(
        &self,
        src_client_id: &ClientIdA<Self>,
        dst_client_id: &ClientIdB<Self>,
        src_chain: ChainA<Self>,
        dst_chain: ChainB<Self>,
    ) -> Result<RelayAToB<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayBToAFromChains: HasBiRelayType + HasErrorType {
    async fn build_relay_b_to_a_from_chains(
        &self,
        src_client_id: &ClientIdB<Self>,
        dst_client_id: &ClientIdA<Self>,
        src_chain: ChainB<Self>,
        dst_chain: ChainA<Self>,
    ) -> Result<RelayBToA<Self>, Self::Error>;
}

#[async_trait]
pub trait RelayAToBBuilder<Builder>: Async
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_relay_a_to_b(
        builder: &Builder,
        src_chain_id: &ChainIdA<Builder>,
        dst_chain_id: &ChainIdB<Builder>,
        src_client_id: &ClientIdA<Builder>,
        dst_client_id: &ClientIdB<Builder>,
    ) -> Result<RelayAToB<Builder>, Builder::Error>;
}

#[async_trait]
pub trait RelayBToABuilder<Builder>: Async
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_relay_b_to_a(
        builder: &Builder,
        src_chain_id: &ChainIdB<Builder>,
        dst_chain_id: &ChainIdA<Builder>,
        src_client_id: &ClientIdB<Builder>,
        dst_client_id: &ClientIdA<Builder>,
    ) -> Result<RelayBToA<Builder>, Builder::Error>;
}
