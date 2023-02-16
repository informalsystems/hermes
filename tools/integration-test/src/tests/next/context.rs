use async_trait::async_trait;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_cosmos::base::traits::builder::{CosmosBuilderTypes, CosmosBuilder};
use ibc_relayer_cosmos::base::types::birelay::CosmosBiRelayWrapper;
use ibc_relayer_cosmos::base::types::chain::CosmosChainWrapper;
use ibc_relayer_cosmos::base::types::relay::CosmosRelayWrapper;
use ibc_relayer_cosmos::contexts::full::birelay::FullCosmosBiRelay;
use ibc_relayer_cosmos::contexts::full::chain::FullCosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::{new_relay_context_with_batch, FullCosmosRelay};
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_runtime::tokio::error::Error as TokioRuntimeError;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_test_framework::error::{handle_generic_error, Error};
use ibc_test_framework::types::binary::chains::ConnectedChains;
use opentelemetry::global;
use std::collections::HashMap;
use std::sync::Arc;

pub struct CosmosRelayBuilder<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    pub chains: ConnectedChains<ChainA, ChainB>,
    pub filter: PacketFilter,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
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


#[async_trait]
impl<ChainA, ChainB> CosmosBuilder for CosmosRelayBuilder<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    fn runtime(&self) ->  &OfaRuntimeWrapper<TokioRuntimeContext>  {
        todo!()
    }

    fn runtime_error(e: TokioRuntimeError) -> Self::Error {
        todo!()
    }

    fn chain_id_a(&self) -> ChainId {
        todo!()
    }

    fn chain_id_b(&self) -> ChainId {
        todo!()
    }

    fn client_id_a(&self) -> ClientId {
        todo!()
    }

    fn client_id_b(&self) -> ClientId {
        todo!()
    }

    async fn build_chain_a(&self) -> Result<FullCosmosChainContext<ChainA>, Self::Error> {
        todo!()
    }

    async fn build_chain_b(&self) -> Result<FullCosmosChainContext<ChainB>, Self::Error> {
        todo!()
    }

    async fn build_relay_a_to_b(
        &self,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainA>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainB>>>,
    ) -> Result<FullCosmosRelay<ChainA, ChainB>, Self::Error> {
        todo!()
    }

    async fn build_relay_b_to_a(
        &self,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainB>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<ChainA>>>,
    ) -> Result<FullCosmosRelay<ChainB, ChainA>, Self::Error> {
        todo!()
    }

    async fn build_birelay(
        &self,
        relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainA, ChainB>>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainB, ChainA>>>,
    ) -> Result<Self::BiRelay, Self::Error> {
        todo!()
    }

    fn chain_a_cache(&self) ->  &ibc_relayer_cosmos::base::traits::builder::ChainACache<Self>  {
        todo!()
    }

    fn chain_b_cache(&self) ->  &ibc_relayer_cosmos::base::traits::builder::ChainBCache<Self>  {
        todo!()
    }

    fn relay_a_to_b_cache(&self) ->  &ibc_relayer_cosmos::base::traits::builder::RelayAToBCache<Self>  {
        todo!()
    }

    fn relay_b_to_a_cache(&self) ->  &ibc_relayer_cosmos::base::traits::builder::RelayBToACache<Self>  {
        todo!()
    }
}

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

    let chain_a = OfaChainWrapper::new(CosmosChainWrapper::new(Arc::new(
        FullCosmosChainContext::new(
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
            runtime.clone(),
            telemetry.clone(),
        ),
    )));

    let chain_b = OfaChainWrapper::new(CosmosChainWrapper::new(Arc::new(
        FullCosmosChainContext::new(
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
            runtime.clone(),
            telemetry,
        ),
    )));

    let relay_a_to_b = new_relay_context_with_batch(
        runtime.clone(),
        chain_a.clone(),
        chain_b.clone(),
        chains.foreign_clients.client_a_to_b.clone(),
        chains.foreign_clients.client_b_to_a.clone(),
        filter.clone(),
        Default::default(),
    );

    let relay_b_to_a = new_relay_context_with_batch(
        runtime.clone(),
        chain_b,
        chain_a,
        chains.foreign_clients.client_b_to_a.clone(),
        chains.foreign_clients.client_a_to_b.clone(),
        filter,
        Default::default(),
    );

    let birelay = OfaBiRelayWrapper::new(CosmosBiRelayWrapper::new(FullCosmosBiRelay::new(
        runtime,
        relay_a_to_b,
        relay_b_to_a,
    )));

    Ok(birelay)
}
