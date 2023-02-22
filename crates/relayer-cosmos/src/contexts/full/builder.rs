use alloc::sync::Arc;
use async_trait::async_trait;
use eyre::eyre;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer::spawn::spawn_chain_runtime;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::batch::types::config::BatchConfig;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_framework::full::one_for_all::types::builder::OfaFullBuilderWrapper;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use opentelemetry::global;
use std::collections::HashMap;
use tokio::runtime::Runtime as TokioRuntime;

use crate::base::error::{BaseError, Error};
use crate::base::traits::builder::CosmosBuilderTypes;
use crate::base::traits::chain::CosmosChain;
use crate::base::types::builder::CosmosBuilderWrapper;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::contexts::full::birelay::FullCosmosBiRelay;
use crate::contexts::full::chain::FullCosmosChainContext;
use crate::contexts::full::relay::FullCosmosRelay;
use crate::full::traits::builder::CosmosFullBuilder;
use crate::full::types::batch::CosmosBatchSender;
use crate::full::types::telemetry::{CosmosTelemetry, TelemetryState};

pub struct CosmosRelayBuilder {
    pub config: Arc<Config>,
    pub filter: PacketFilter,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub batch_config: BatchConfig,
}

impl CosmosBuilderTypes for CosmosRelayBuilder {
    type Preset = FullPreset;

    type Error = Error;

    type BiRelay = FullCosmosBiRelay<BaseChainHandle, BaseChainHandle>;
}

#[allow(unused)]
#[async_trait]
impl CosmosFullBuilder for CosmosRelayBuilder {
    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn runtime_error(e: TokioRuntimeError) -> Error {
        BaseError::tokio(e).into()
    }

    fn batch_config(&self) -> &BatchConfig {
        &self.batch_config
    }

    async fn build_chain_a(
        &self,
        chain_id: &ChainId,
    ) -> Result<FullCosmosChainContext<BaseChainHandle>, Error> {
        tokio::task::block_in_place(|| {
            self.build_chain(chain_id, self.runtime.runtime.runtime.clone())
        })
    }

    async fn build_chain_b(
        &self,
        chain_id: &ChainId,
    ) -> Result<FullCosmosChainContext<BaseChainHandle>, Self::Error> {
        tokio::task::block_in_place(|| {
            self.build_chain(chain_id, self.runtime.runtime.runtime.clone())
        })
    }

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<BaseChainHandle>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<BaseChainHandle>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<FullCosmosRelay<BaseChainHandle, BaseChainHandle>, Self::Error> {
        self.build_relay(
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
    }

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<BaseChainHandle>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<BaseChainHandle>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<FullCosmosRelay<BaseChainHandle, BaseChainHandle>, Self::Error> {
        self.build_relay(
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
    }

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<
            CosmosRelayWrapper<FullCosmosRelay<BaseChainHandle, BaseChainHandle>>,
        >,
        relay_b_to_a: OfaRelayWrapper<
            CosmosRelayWrapper<FullCosmosRelay<BaseChainHandle, BaseChainHandle>>,
        >,
    ) -> Result<Self::BiRelay, Self::Error> {
        let birelay = FullCosmosBiRelay::new(self.runtime.clone(), relay_a_to_b, relay_b_to_a);

        Ok(birelay)
    }
}

impl CosmosRelayBuilder {
    pub fn new(config: Arc<Config>, runtime: Arc<TokioRuntime>) -> Self {
        let telemetry = OfaTelemetryWrapper::new(CosmosTelemetry::new(TelemetryState {
            meter: global::meter("hermes"),
            counters: HashMap::new(),
            value_recorders: HashMap::new(),
            updown_counters: HashMap::new(),
        }));

        let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(runtime));

        Self {
            config,
            filter: PacketFilter::default(),
            telemetry,
            runtime,
            batch_config: BatchConfig::default(),
        }
    }

    pub fn new_wrapped(
        config: Arc<Config>,
        runtime: Arc<TokioRuntime>,
    ) -> OfaFullBuilderWrapper<CosmosBuilderWrapper<Self>> {
        OfaFullBuilderWrapper::new_with_homogenous_cache(CosmosBuilderWrapper::new(Self::new(
            config, runtime,
        )))
    }

    pub fn build_chain(
        &self,
        chain_id: &ChainId,
        runtime: Arc<TokioRuntime>,
    ) -> Result<FullCosmosChainContext<BaseChainHandle>, Error> {
        let handle = spawn_chain_runtime::<BaseChainHandle>(&self.config, chain_id, runtime)
            .map_err(BaseError::spawn)?;

        let signer = handle.get_signer().map_err(BaseError::relayer)?;

        let keypair = handle.get_key().map_err(BaseError::relayer)?;

        let AnySigningKeyPair::Secp256k1(key) = keypair else {
            return Err(BaseError::generic(eyre!("no Secp256k1 key pair for chain {}", chain_id)).into());
        };

        let chain_config = handle.config().map_err(BaseError::relayer)?;
        let websocket_addr = chain_config.websocket_addr.clone();
        let tx_config = TxConfig::try_from(&chain_config).map_err(BaseError::relayer)?;

        let context = FullCosmosChainContext::new(
            handle,
            signer,
            tx_config,
            websocket_addr,
            key,
            self.runtime.clone(),
            self.telemetry.clone(),
        );

        Ok(context)
    }

    pub fn build_relay(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<BaseChainHandle>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<BaseChainHandle>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<FullCosmosRelay<BaseChainHandle, BaseChainHandle>, Error> {
        let client_src_to_dst = ForeignClient::restore(
            dst_client_id.clone(),
            dst_chain.chain.chain.chain_handle().clone(),
            src_chain.chain.chain.chain_handle().clone(),
        );

        let client_dst_to_src = ForeignClient::restore(
            src_client_id.clone(),
            src_chain.chain.chain.chain_handle().clone(),
            dst_chain.chain.chain.chain_handle().clone(),
        );

        let relay = FullCosmosRelay::new(
            self.runtime.clone(),
            src_chain,
            dst_chain,
            client_src_to_dst,
            client_dst_to_src,
            self.filter.clone(),
            src_batch_sender,
            dst_batch_sender,
        );

        Ok(relay)
    }
}
