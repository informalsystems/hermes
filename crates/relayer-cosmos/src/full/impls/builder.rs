use alloc::sync::Arc;

use async_trait::async_trait;
use ibc_relayer_all_in_one::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::extra::one_for_all::traits::builder::OfaFullBuilder;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::base::traits::builder::{ChainA, ChainB, RelayAToB, RelayBToA};
use crate::base::types::birelay::CosmosBiRelayWrapper;
use crate::base::types::builder::CosmosBuilderWrapper;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::full::traits::builder::CosmosFullBuilder;
use crate::full::types::batch::CosmosBatchSender;

#[async_trait]
impl<Builder> OfaFullBuilder for CosmosBuilderWrapper<Builder>
where
    Builder: CosmosFullBuilder,
{
    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        self.builder.runtime()
    }

    fn runtime_error(e: TokioRuntimeError) -> Builder::Error {
        Builder::runtime_error(e)
    }

    fn batch_config(&self) -> &BatchConfig {
        self.builder.batch_config()
    }

    async fn build_chain_a(
        &self,
        chain_id: &ChainId,
    ) -> Result<CosmosChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = self.builder.build_chain_a(chain_id).await?;

        Ok(CosmosChainWrapper::new(Arc::new(chain)))
    }

    async fn build_chain_b(
        &self,
        chain_id: &ChainId,
    ) -> Result<CosmosChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = self.builder.build_chain_b(chain_id).await?;

        Ok(CosmosChainWrapper::new(Arc::new(chain)))
    }

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Builder>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Builder>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<CosmosRelayWrapper<RelayAToB<Builder>>, Builder::Error> {
        let relay = self
            .builder
            .build_relay_a_to_b(
                src_client_id,
                dst_client_id,
                src_chain,
                dst_chain,
                src_batch_sender,
                dst_batch_sender,
            )
            .await?;

        Ok(CosmosRelayWrapper::new(relay))
    }

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<ChainB<Builder>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<ChainA<Builder>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<CosmosRelayWrapper<RelayBToA<Builder>>, Builder::Error> {
        let relay = self
            .builder
            .build_relay_b_to_a(
                src_client_id,
                dst_client_id,
                src_chain,
                dst_chain,
                src_batch_sender,
                dst_batch_sender,
            )
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
}
