use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_cosmos::contexts::full::chain::FullCosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::new_relay_context_with_batch;
use ibc_relayer_cosmos::full::all_for_one::relay::AfoCosmosFullRelay;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_test_framework::error::{handle_generic_error, Error};
use ibc_test_framework::types::binary::chains::ConnectedChains;
use opentelemetry::global;
use std::collections::HashMap;

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    chains: &ConnectedChains<ChainA, ChainB>,
    filter: PacketFilter,
) -> Result<impl AfoCosmosFullRelay, Error>
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

    let chain_a = FullCosmosChainContext::new(
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
        telemetry.clone(),
    );

    let chain_b = FullCosmosChainContext::new(
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
        telemetry,
    );

    let relay = new_relay_context_with_batch(
        runtime,
        chain_a,
        chain_b,
        chains.foreign_clients.client_a_to_b.clone(),
        chains.foreign_clients.client_b_to_a.clone(),
        filter,
        Default::default(),
    );

    Ok(relay)
}
