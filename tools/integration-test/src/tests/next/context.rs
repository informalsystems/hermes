use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_cosmos::cosmos::context::chain::CosmosChainContext;
use ibc_relayer_cosmos::cosmos::context::relay::CosmosRelayContext;
use ibc_relayer_cosmos::tokio::context::TokioRuntimeContext;
use ibc_relayer_framework::extras::batch::spawn::{
    BatchMessageWorkerSpawner, CanSpawnBatchMessageWorker,
};
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;
use ibc_relayer_framework::traits::target::{DestinationTarget, SourceTarget};
use ibc_test_framework::types::binary::chains::ConnectedChains;

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    chains: &ConnectedChains<ChainA, ChainB>,
) -> OfaRelayContext<CosmosRelayContext<ChainA, ChainB>>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let runtime = TokioRuntimeContext::new(chains.node_a.value().chain_driver.runtime.clone());

    let (handler_a, receiver_a) = CosmosChainContext::new(
        runtime.clone(),
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
    );

    let (handler_b, receiver_b) = CosmosChainContext::new(
        runtime.clone(),
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
    );

    let relay = CosmosRelayContext::new(
        runtime,
        handler_a.clone(),
        handler_b.clone(),
        chains.foreign_clients.client_a_to_b.clone(),
        chains.foreign_clients.client_b_to_a.clone(),
    );

    let relay_context = OfaRelayContext::new(relay);

    <BatchMessageWorkerSpawner<SourceTarget>>::spawn_batch_message_worker(
        relay_context.clone(),
        Default::default(),
        receiver_a,
    );

    <BatchMessageWorkerSpawner<DestinationTarget>>::spawn_batch_message_worker(
        relay_context.clone(),
        Default::default(),
        receiver_b,
    );

    relay_context
}
