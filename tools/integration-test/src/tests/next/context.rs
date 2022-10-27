use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_cosmos::contexts::full::chain::CosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::new_relay_context_with_batch;
use ibc_relayer_cosmos::full::all_for_one::relay::AfoCosmosFullRelay;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::common::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_test_framework::relayer_mock::contexts::chain::MockChainContext;
use ibc_test_framework::relayer_mock::contexts::relay::MockRelayContext;
use ibc_test_framework::types::binary::chains::ConnectedChains;

use opentelemetry::global;
use tokio::runtime::Runtime;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    chains: &ConnectedChains<ChainA, ChainB>,
    filter: PacketFilter,
) -> impl AfoCosmosFullRelay
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let telemetry = CosmosTelemetry::new(Arc::new(Mutex::new(TelemetryState {
        meter: global::meter("hermes"),
        counters: HashMap::new(),
        value_recorders: HashMap::new(),
        updown_counters: HashMap::new(),
    })));

    let runtime = TokioRuntimeContext::new(chains.node_a.value().chain_driver.runtime.clone());

    let chain_a = CosmosChainContext::new(
        chains.handle_a.clone(),
        chains
            .node_a
            .value()
            .wallets
            .relayer
            .address
            .0
            .parse()
            .unwrap(),
        chains.node_a.value().chain_driver.tx_config.clone(),
        chains.node_a.value().wallets.relayer.key.clone(),
        telemetry.clone(),
    );

    let chain_b = CosmosChainContext::new(
        chains.handle_b.clone(),
        chains
            .node_b
            .value()
            .wallets
            .relayer
            .address
            .0
            .parse()
            .unwrap(),
        chains.node_b.value().chain_driver.tx_config.clone(),
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

    relay
}

pub fn build_mock_relay_context(
) -> OfaRelayWrapper<MockRelayContext> {
    let runtime = TokioRuntimeContext::new(Arc::new(Runtime::new().unwrap()));
    let mock_relay = MockRelayContext::new(
        Arc::new(OfaChainWrapper { chain: MockChainContext::default() }),
        Arc::new(OfaChainWrapper { chain: MockChainContext::default() }),
        String::from("client_a"),
        String::from("client_b"),
        runtime,
    );

    let relay = OfaRelayWrapper::new(mock_relay);

    relay
}
