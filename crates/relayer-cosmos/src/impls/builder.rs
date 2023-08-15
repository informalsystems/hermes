use async_trait::async_trait;
use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer_all_in_one::one_for_all::traits::builder::OfaBuilder;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;
use ibc_relayer_runtime::types::error::Error as TokioRuntimeError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::contexts::birelay::CosmosBiRelay;
use crate::contexts::builder::CosmosBuilder;
use crate::contexts::chain::CosmosChain;
use crate::contexts::relay::CosmosRelay;
use crate::types::batch::CosmosBatchSender;
use crate::types::error::{BaseError, Error};

#[async_trait]
impl OfaBuilder for CosmosBuilder {
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type BiRelay = CosmosBiRelay<BaseChainHandle, BaseChainHandle>;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn runtime_error(e: TokioRuntimeError) -> Error {
        BaseError::tokio(e).into()
    }

    fn birelay_error(e: Error) -> Error {
        e
    }

    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }

    async fn build_chain_a(
        &self,
        chain_id: &ChainId,
    ) -> Result<CosmosChain<BaseChainHandle>, Error> {
        let chain = self.build_chain(chain_id).await?;

        Ok(chain)
    }

    async fn build_chain_b(
        &self,
        chain_id: &ChainId,
    ) -> Result<CosmosChain<BaseChainHandle>, Error> {
        let chain = self.build_chain(chain_id).await?;

        Ok(chain)
    }

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        dst_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<CosmosRelay<BaseChainHandle, BaseChainHandle>, Error> {
        let relay = self.build_relay(
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )?;

        Ok(relay)
    }

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        dst_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<CosmosRelay<BaseChainHandle, BaseChainHandle>, Error> {
        let relay = self.build_relay(
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )?;

        Ok(relay)
    }

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<CosmosRelay<BaseChainHandle, BaseChainHandle>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelay<BaseChainHandle, BaseChainHandle>>,
    ) -> Result<CosmosBiRelay<BaseChainHandle, BaseChainHandle>, Error> {
        let birelay = CosmosBiRelay::new(self.runtime.clone(), relay_a_to_b, relay_b_to_a);

        Ok(birelay)
    }

    fn batch_config(&self) -> &BatchConfig {
        &self.batch_config
    }
}
