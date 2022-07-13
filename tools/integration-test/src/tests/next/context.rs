use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_cosmos::cosmos::context::chain::CosmosChainContext;
use ibc_relayer_cosmos::cosmos::context::relay::CosmosRelayContext;
use ibc_test_framework::types::binary::chains::ConnectedChains;

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    chains: &ConnectedChains<ChainA, ChainB>,
) -> CosmosRelayContext<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let handler_a = CosmosChainContext {
        handle: chains.handle_a.clone(),
        signer: chains
            .node_a
            .value()
            .wallets
            .relayer
            .address
            .0
            .parse()
            .unwrap(),
        tx_config: chains.node_a.value().chain_driver.tx_config.clone(),
        key_entry: chains.node_a.value().wallets.relayer.key.clone(),
    };

    let handler_b = CosmosChainContext {
        handle: chains.handle_b.clone(),
        signer: chains
            .node_b
            .value()
            .wallets
            .relayer
            .address
            .0
            .parse()
            .unwrap(),
        tx_config: chains.node_b.value().chain_driver.tx_config.clone(),
        key_entry: chains.node_b.value().wallets.relayer.key.clone(),
    };

    let relay_handler = CosmosRelayContext {
        src_handle: handler_a,
        dst_handle: handler_b,
        src_to_dst_client: chains.foreign_clients.client_a_to_b.clone(),
        dst_to_src_client: chains.foreign_clients.client_b_to_a.clone(),
    };

    relay_handler
}
