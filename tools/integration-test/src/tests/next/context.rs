use async_trait::async_trait;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_cosmos::base::traits::builder::CosmosBuilderTypes;
use ibc_relayer_cosmos::base::types::builder::CosmosBuilderWrapper;
use ibc_relayer_cosmos::base::types::chain::CosmosChainWrapper;
use ibc_relayer_cosmos::base::types::relay::CosmosRelayWrapper;
use ibc_relayer_cosmos::contexts::full::birelay::FullCosmosBiRelay;
use ibc_relayer_cosmos::contexts::full::chain::FullCosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::FullCosmosRelay;
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use ibc_relayer_cosmos::full::traits::builder::CosmosFullBuilder;
use ibc_relayer_cosmos::full::types::batch::CosmosBatchSender;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::all_for_one::builder::CanBuildAfoFullBiRelay;
use ibc_relayer_framework::full::batch::types::config::BatchConfig;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_framework::full::one_for_all::types::builder::OfaFullBuilderWrapper;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_test_framework::error::{handle_generic_error, Error};
use ibc_test_framework::types::binary::chains::ConnectedChains;
use opentelemetry::global;
use std::collections::HashMap;

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    chains: &ConnectedChains<ChainA, ChainB>,
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

    let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(
        chains.node_a.value().chain_driver.runtime.clone(),
    ));

    let builder = OfaFullBuilderWrapper::new_with_heterogenous_cache(CosmosBuilderWrapper::new(
        CosmosRelayBuilder {
            chains: chains.clone(),
            filter,
            telemetry,
            runtime: runtime.clone(),
            batch_config: BatchConfig::default(),
        },
    ));

    let birelay = runtime
        .runtime
        .runtime
        .block_on(builder.build_afo_full_birelay(
            chains.chain_id_a().value(),
            chains.chain_id_b().value(),
            chains.client_id_a().value(),
            chains.client_id_b().value(),
        ))?;

    Ok(birelay)
}

pub struct CosmosRelayBuilder<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    pub chains: ConnectedChains<ChainA, ChainB>,
    pub filter: PacketFilter,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub batch_config: BatchConfig,
}

impl<ChainA, ChainB> CosmosBuilderTypes for CosmosRelayBuilder<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    type Preset = FullPreset;

    type Error = Error;

    type BiRelay = FullCosmosBiRelay<ChainA, ChainB>;
}

#[allow(unused)]
#[async_trait]
impl<ChainA, ChainB> CosmosFullBuilder for CosmosRelayBuilder<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
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
    ) -> Result<FullCosmosChainContext<ChainA>, Self::Error> {
        let chains = &self.chains;

        let context = FullCosmosChainContext::new(
            chains.handle_a.clone(),
            chains
                .node_a
                .value()
                .wallets
                .relayer
                .address
                .0
                .parse()
                .map_err(handle_generic_error)?,
            chains.node_a.value().chain_driver.tx_config.clone(),
            chains
                .node_a
                .value()
                .chain_driver
                .websocket_address()
                .parse()
                .map_err(handle_generic_error)?,
            chains.node_a.value().wallets.relayer.key.clone(),
            self.runtime.clone(),
            self.telemetry.clone(),
        );

        Ok(context)
    }

    async fn build_chain_b(
        &self,
        chain_id: &ChainId,
    ) -> Result<FullCosmosChainContext<ChainB>, Self::Error> {
        let chains = &self.chains;

        let context = FullCosmosChainContext::new(
            chains.handle_b.clone(),
            chains
                .node_b
                .value()
                .wallets
                .relayer
                .address
                .0
                .parse()
                .map_err(handle_generic_error)?,
            chains.node_b.value().chain_driver.tx_config.clone(),
            chains
                .node_b
                .value()
                .chain_driver
                .websocket_address()
                .parse()
                .map_err(handle_generic_error)?,
            chains.node_b.value().wallets.relayer.key.clone(),
            self.runtime.clone(),
            self.telemetry.clone(),
        );

        Ok(context)
    }

    async fn build_relay_a_to_b(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainA>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainB>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<FullCosmosRelay<ChainA, ChainB>, Self::Error> {
        let relay = FullCosmosRelay::new(
            self.runtime.clone(),
            src_chain,
            dst_chain,
            self.chains.foreign_clients.client_a_to_b.clone(),
            self.chains.foreign_clients.client_b_to_a.clone(),
            self.filter.clone(),
            src_batch_sender,
            dst_batch_sender,
        );

        Ok(relay)
    }

    async fn build_relay_b_to_a(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainB>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainA>>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<FullCosmosRelay<ChainB, ChainA>, Self::Error> {
        let relay = FullCosmosRelay::new(
            self.runtime.clone(),
            src_chain,
            dst_chain,
            self.chains.foreign_clients.client_b_to_a.clone(),
            self.chains.foreign_clients.client_a_to_b.clone(),
            self.filter.clone(),
            src_batch_sender,
            dst_batch_sender,
        );

        Ok(relay)
    }

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainA, ChainB>>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainB, ChainA>>>,
    ) -> Result<Self::BiRelay, Self::Error> {
        let birelay = FullCosmosBiRelay::new(self.runtime.clone(), relay_a_to_b, relay_b_to_a);

        Ok(birelay)
    }
}
