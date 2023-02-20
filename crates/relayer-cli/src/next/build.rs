use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer_cosmos::base::traits::builder::CosmosBuilderTypes;
use ibc_relayer_cosmos::base::traits::chain::CosmosChain;
use ibc_relayer_cosmos::base::types::builder::CosmosBuilderWrapper;
use ibc_relayer_cosmos::base::types::chain::CosmosChainWrapper;
use ibc_relayer_cosmos::base::types::relay::CosmosRelayWrapper;
use ibc_relayer_cosmos::contexts::full::birelay::FullCosmosBiRelay;
use ibc_relayer_cosmos::contexts::full::chain::FullCosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::new_relay_context_with_batch;
use ibc_relayer_cosmos::contexts::full::relay::FullCosmosRelay;
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use ibc_relayer_cosmos::full::traits::builder::CosmosFullBuilder;
use ibc_relayer_cosmos::full::types::batch::CosmosBatchSender;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::base::relay::types::two_way::TwoWayRelayContext;
use ibc_relayer_framework::full::batch::types::config::BatchConfig;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_framework::full::one_for_all::types::builder::OfaFullBuilderWrapper;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_framework::full::relay::impls::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use opentelemetry::global;
use std::collections::HashMap;
use tokio::runtime::Runtime as TokioRuntime;

use crate::cli_utils::spawn_chain_runtime_generic;
use crate::error::Error;

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
        Error::generic(e.into())
    }

    fn batch_config(&self) -> &BatchConfig {
        &self.batch_config
    }

    async fn build_chain_a(
        &self,
        chain_id: &ChainId,
    ) -> Result<FullCosmosChainContext<BaseChainHandle>, Error> {
        tokio::task::block_in_place(|| self.build_chain(chain_id))
    }

    async fn build_chain_b(
        &self,
        chain_id: &ChainId,
    ) -> Result<FullCosmosChainContext<BaseChainHandle>, Self::Error> {
        tokio::task::block_in_place(|| self.build_chain(chain_id))
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
    ) -> Result<FullCosmosChainContext<BaseChainHandle>, Error> {
        let handle = spawn_chain_runtime_generic::<BaseChainHandle>(&self.config, chain_id)?;

        let signer = handle.get_signer().map_err(Error::relayer)?;

        let keypair = handle.get_key().map_err(Error::relayer)?;

        let AnySigningKeyPair::Secp256k1(key) = keypair else {
            return Err(Error::secp256k1_key_pair(handle.id()));
        };

        let chain_config = handle.config().map_err(Error::relayer)?;
        let websocket_addr = chain_config.websocket_addr.clone();
        let tx_config = TxConfig::try_from(&chain_config).map_err(Error::relayer)?;

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

/// Initializes a Cosmos relay context that utilizes the experimental relayer
/// architecture for relaying packets between two Cosmos chains.
pub fn build_cosmos_birelay_context<ChainA, ChainB>(
    handle_a: ChainA,
    handle_b: ChainB,
    client_id_a: ClientId,
    client_id_b: ClientId,
    runtime: Arc<TokioRuntime>,
    filter: PacketFilter,
) -> Result<impl AfoCosmosFullBiRelay, Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let telemetry = OfaTelemetryWrapper::new(CosmosTelemetry::new(TelemetryState {
        meter: global::meter("hermes"),
        counters: HashMap::new(),
        value_recorders: HashMap::new(),
        updown_counters: HashMap::new(),
    }));

    let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(runtime));

    let chain_a_signer = handle_a.get_signer().map_err(Error::relayer)?;
    let chain_b_signer = handle_b.get_signer().map_err(Error::relayer)?;

    let chain_a_keypair = handle_a.get_key().map_err(Error::relayer)?;
    let chain_b_keypair = handle_b.get_key().map_err(Error::relayer)?;

    let AnySigningKeyPair::Secp256k1(chain_a_key) = chain_a_keypair else {
        return Err(Error::secp256k1_key_pair(handle_a.id()));
    };

    let AnySigningKeyPair::Secp256k1(chain_b_key) = chain_b_keypair else {
        return Err(Error::secp256k1_key_pair(handle_b.id()));
    };

    let chain_a_config = handle_a.config().map_err(Error::relayer)?;
    let chain_a_websocket_addr = chain_a_config.websocket_addr.clone();
    let chain_a_config = TxConfig::try_from(&chain_a_config).map_err(Error::relayer)?;

    let chain_b_config = handle_b.config().map_err(Error::relayer)?;
    let chain_b_websocket_addr = chain_b_config.websocket_addr.clone();
    let chain_b_config = TxConfig::try_from(&chain_b_config).map_err(Error::relayer)?;

    let chain_a = OfaChainWrapper::new(CosmosChainWrapper::new(Arc::new(
        FullCosmosChainContext::new(
            handle_a.clone(),
            chain_a_signer,
            chain_a_config,
            chain_a_websocket_addr,
            chain_a_key,
            runtime.clone(),
            telemetry.clone(),
        ),
    )));

    let chain_b = OfaChainWrapper::new(CosmosChainWrapper::new(Arc::new(
        FullCosmosChainContext::new(
            handle_b.clone(),
            chain_b_signer,
            chain_b_config,
            chain_b_websocket_addr,
            chain_b_key,
            runtime.clone(),
            telemetry,
        ),
    )));

    let client_a_to_b = ForeignClient::restore(client_id_b, handle_b.clone(), handle_a.clone());
    let client_b_to_a = ForeignClient::restore(client_id_a, handle_a, handle_b);

    let relay_a_to_b = new_relay_context_with_batch(
        runtime.clone(),
        chain_a.clone(),
        chain_b.clone(),
        client_a_to_b.clone(),
        client_b_to_a.clone(),
        filter.clone(),
        Default::default(),
    );

    let relay_b_to_a = new_relay_context_with_batch(
        runtime,
        chain_b,
        chain_a,
        client_b_to_a,
        client_a_to_b,
        filter,
        Default::default(),
    );

    let birelay = TwoWayRelayContext::new(ParallelTwoWayAutoRelay, relay_a_to_b, relay_b_to_a);

    Ok(birelay)
}
