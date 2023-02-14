use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_relayer_framework::base::one_for_all::traits::builder::{OfaBuilder, OfaBuilderTypes};
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::base::traits::builder::{
    ChainA, ChainACache, ChainB, ChainBCache, CosmosBuilder, CosmosBuilderTypes, RelayAToB,
    RelayAToBCache, RelayBToA, RelayBToACache,
};
use crate::base::types::birelay::CosmosBiRelayWrapper;
use crate::base::types::builder::CosmosBuilderWrapper;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;

impl<Builder> OfaBuilderTypes for CosmosBuilderWrapper<Builder>
where
    Builder: CosmosBuilderTypes,
{
    type Preset = Builder::Preset;

    type Error = Builder::Error;

    type Runtime = TokioRuntimeContext;

    type BiRelay = CosmosBiRelayWrapper<Builder::BiRelay>;
}

#[async_trait]
impl<Builder> OfaBuilder for CosmosBuilderWrapper<Builder>
where
    Builder: CosmosBuilder,
{
    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        self.builder.runtime()
    }

    fn runtime_error(e: TokioRuntimeError) -> Builder::Error {
        Builder::runtime_error(e)
    }

    fn chain_id_a(&self) -> ChainId {
        self.builder.chain_id_a()
    }

    fn chain_id_b(&self) -> ChainId {
        self.builder.chain_id_b()
    }

    fn client_id_a(&self) -> ClientId {
        self.builder.client_id_a()
    }

    fn client_id_b(&self) -> ClientId {
        self.builder.client_id_b()
    }

    async fn build_chain_a(&self) -> Result<CosmosChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = self.builder.build_chain_a().await?;

        Ok(CosmosChainWrapper::new(Arc::new(chain)))
    }

    async fn build_chain_b(&self) -> Result<CosmosChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = self.builder.build_chain_b().await?;

        Ok(CosmosChainWrapper::new(Arc::new(chain)))
    }

    async fn build_relay_a_to_b(
        &self,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Builder>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Builder>>>,
    ) -> Result<CosmosRelayWrapper<RelayAToB<Builder>>, Builder::Error> {
        let relay = self
            .builder
            .build_relay_a_to_b(src_chain, dst_chain)
            .await?;

        Ok(CosmosRelayWrapper::new(relay))
    }

    async fn build_relay_b_to_a(
        &self,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Builder>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Builder>>>,
    ) -> Result<CosmosRelayWrapper<RelayBToA<Builder>>, Builder::Error> {
        let relay = self
            .builder
            .build_relay_b_to_a(src_chain, dst_chain)
            .await?;

        Ok(CosmosRelayWrapper::new(relay))
    }

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<RelayAToB<Builder>>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<RelayBToA<Builder>>>,
    ) -> Result<CosmosBiRelayWrapper<Builder::BiRelay>, Builder::Error> {
        let birelay = self
            .builder
            .build_birelay(relay_a_to_b, relay_b_to_a)
            .await?;

        Ok(CosmosBiRelayWrapper::new(birelay))
    }

    fn chain_a_cache(&self) -> &ChainACache<Builder> {
        self.builder.chain_a_cache()
    }

    fn chain_b_cache(&self) -> &ChainBCache<Builder> {
        self.builder.chain_b_cache()
    }

    fn relay_a_to_b_cache(&self) -> &RelayAToBCache<Builder> {
        self.builder.relay_a_to_b_cache()
    }

    fn relay_b_to_a_cache(&self) -> &RelayBToACache<Builder> {
        self.builder.relay_b_to_a_cache()
    }
}
