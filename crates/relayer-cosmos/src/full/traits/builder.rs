use async_trait::async_trait;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::batch::types::config::BatchConfig;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::base::traits::builder::{ChainA, ChainB, CosmosBuilderTypes, RelayAToB, RelayBToA};
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::full::traits::birelay::CosmosFullBiRelay;
use crate::full::types::batch::CosmosBatchSender;

pub trait CosmosFullBuilderTypes: CosmosBuilderTypes<BiRelay = Self::FullBiRelay> {
    type FullBiRelay: CosmosFullBiRelay<Preset = Self::Preset>;
}

impl<Build> CosmosFullBuilderTypes for Build
where
    Build: CosmosBuilderTypes,
    Build::BiRelay: CosmosFullBiRelay,
{
    type FullBiRelay = Build::BiRelay;
}

#[async_trait]
pub trait CosmosFullBuilder: CosmosFullBuilderTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext>;

    fn runtime_error(e: TokioRuntimeError) -> Self::Error;

    fn batch_config(&self) -> &BatchConfig;

    async fn build_chain_a(&self, chain_id: &ChainId) -> Result<ChainA<Self>, Self::Error>;

    async fn build_chain_b(&self, chain_id: &ChainId) -> Result<ChainB<Self>, Self::Error>;

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Self>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Self>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<RelayAToB<Self>, Self::Error>;

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Self>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Self>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<RelayBToA<Self>, Self::Error>;

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<RelayAToB<Self>>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<RelayBToA<Self>>>,
    ) -> Result<Self::BiRelay, Self::Error>;
}
