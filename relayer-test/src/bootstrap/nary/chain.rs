use core::convert::TryInto;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::sync::Arc;
use std::sync::RwLock;

use crate::bootstrap::binary::chain::{
    add_chain_config, add_keys_to_chain_handle, new_registry, save_relayer_config,
};
use crate::error::Error;
use crate::types::config::TestConfig;
use crate::types::nary::chains::{ConnectedChains, DynamicConnectedChains};
use crate::types::single::node::FullNode;

pub fn boostrap_chains_with_nodes<const SIZE: usize>(
    test_config: &TestConfig,
    full_nodes: [FullNode; SIZE],
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ConnectedChains<impl ChainHandle, SIZE>, Error> {
    let connected_chains =
        boostrap_chains_with_any_nodes(test_config, full_nodes.into(), config_modifier)?
            .try_into()?;

    Ok(connected_chains)
}

pub fn boostrap_chains_with_any_nodes(
    test_config: &TestConfig,
    full_nodes: Vec<FullNode>,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<DynamicConnectedChains<impl ChainHandle>, Error> {
    let mut config = Config::default();

    for node in full_nodes.iter() {
        add_chain_config(&mut config, &node)?;
    }

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    let mut chain_handles = Vec::new();

    for node in full_nodes.iter() {
        let handle = spawn_chain_handle(&registry, &node)?;
        chain_handles.push(handle);
    }

    let mut foreign_clients: Vec<Vec<ForeignClient<_, _>>> = Vec::new();

    for handle_a in chain_handles.iter() {
        let mut foreign_clients_b = Vec::new();

        for handle_b in chain_handles.iter() {
            let foreign_client = ForeignClient::unsafe_new(handle_b.clone(), handle_a.clone())?;
            foreign_clients_b.push(foreign_client);
        }

        foreign_clients.push(foreign_clients_b);
    }

    let connected_chains = DynamicConnectedChains {
        config_path,
        config,
        registry,
        chain_handles,
        full_nodes,
        foreign_clients,
    };

    Ok(connected_chains)
}

pub fn spawn_chain_handle<Handle: ChainHandle>(
    registry: &SharedRegistry<Handle>,
    node: &FullNode,
) -> Result<Handle, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry.get_or_spawn(chain_id)?;

    add_keys_to_chain_handle(&handle, &node.wallets)?;

    Ok(handle)
}
