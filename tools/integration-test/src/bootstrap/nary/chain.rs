/*!
   Functions for bootstrapping N-ary number of chains.
*/

use core::convert::TryInto;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::sync::Arc;
use std::sync::RwLock;

use crate::bootstrap::binary::chain::{
    add_chain_config, add_keys_to_chain_handle, bootstrap_foreign_client, new_registry,
    save_relayer_config,
};
use crate::error::{handle_generic_error, Error};
use crate::relayer::driver::RelayerDriver;
use crate::types::config::TestConfig;
use crate::types::nary::chains::{DynamicConnectedChains, NaryConnectedChains};
use crate::types::single::node::FullNode;

/**
  Bootstrap a fixed number of chains specified by `SIZE`.
*/
pub fn boostrap_chains_with_nodes<const SIZE: usize>(
    test_config: &TestConfig,
    full_nodes: [FullNode; SIZE],
    config_modifier: impl FnOnce(&mut Config),
) -> Result<(RelayerDriver, NaryConnectedChains<impl ChainHandle, SIZE>), Error> {
    let (relayer, chains) =
        boostrap_chains_with_any_nodes(test_config, full_nodes.into(), config_modifier)?;

    Ok((relayer, chains.try_into()?))
}

/**
   Bootstrap a fixed number of chains that are actually
   backed by the same underlying full node.
*/
pub fn boostrap_chains_with_self_connected_node<const SIZE: usize>(
    test_config: &TestConfig,
    full_node: FullNode,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<(RelayerDriver, NaryConnectedChains<impl ChainHandle, SIZE>), Error> {
    let full_nodes = vec![full_node; SIZE];
    let (relayer, chains) =
        boostrap_chains_with_any_nodes(test_config, full_nodes, config_modifier)?;

    Ok((relayer, chains.try_into()?))
}

/**
   Bootstrap a dynamic number of chains, according to the number of full nodes
   in the `Vec<FullNode>`.
*/
pub fn boostrap_chains_with_any_nodes(
    test_config: &TestConfig,
    full_nodes: Vec<FullNode>,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<(RelayerDriver, DynamicConnectedChains<impl ChainHandle>), Error> {
    let mut config = Config::default();

    for node in full_nodes.iter() {
        add_chain_config(&mut config, node)?;
    }

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    let mut chain_handles = Vec::new();

    for node in full_nodes.iter() {
        let handle = spawn_chain_handle(&registry, node)?;
        chain_handles.push(handle);
    }

    let mut foreign_clients: Vec<Vec<ForeignClient<_, _>>> = Vec::new();

    for handle_a in chain_handles.iter() {
        let mut foreign_clients_b = Vec::new();

        for handle_b in chain_handles.iter() {
            let foreign_client = bootstrap_foreign_client(handle_a, handle_b)?;
            foreign_clients_b.push(foreign_client);
        }

        foreign_clients.push(foreign_clients_b);
    }

    let relayer = RelayerDriver {
        config_path,
        config,
        registry,
        hang_on_fail: test_config.hang_on_fail,
    };

    let connected_chains = DynamicConnectedChains::new(chain_handles, full_nodes, foreign_clients);

    Ok((relayer, connected_chains))
}

fn spawn_chain_handle<Handle: ChainHandle>(
    registry: &SharedRegistry<Handle>,
    node: &FullNode,
) -> Result<Handle, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry
        .get_or_spawn(chain_id)
        .map_err(handle_generic_error)?;

    add_keys_to_chain_handle(&handle, &node.wallets)?;

    Ok(handle)
}
