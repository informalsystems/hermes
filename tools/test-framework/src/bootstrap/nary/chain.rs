/*!
   Functions for bootstrapping N-ary number of chains.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::registry::SharedRegistry;

use crate::bootstrap::binary::chain::{
    add_chain_config, add_keys_to_chain_handle, new_registry, save_relayer_config,
};
use crate::error::{handle_generic_error, Error};
use crate::relayer::driver::RelayerDriver;
use crate::types::config::TestConfig;
use crate::types::nary::chains::{DynamicConnectedChains, NaryConnectedChains};
use crate::types::single::node::FullNode;
use crate::types::topology::{bootstrap_topology, TopologyType};

/**
  Bootstrap a fixed number of chains specified by `SIZE`.
*/
pub fn boostrap_chains_with_nodes<const SIZE: usize>(
    test_config: &TestConfig,
    full_nodes: [FullNode; SIZE],
    topology_override: Option<TopologyType>,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<(RelayerDriver, NaryConnectedChains<impl ChainHandle, SIZE>), Error> {
    let (relayer, chains) = boostrap_chains_with_any_nodes(
        test_config,
        full_nodes.into(),
        topology_override,
        config_modifier,
    )?;

    Ok((relayer, chains.try_into()?))
}

/**
   Bootstrap a fixed number of chains that are actually
   backed by the same underlying full node.
*/
pub fn boostrap_chains_with_self_connected_node<const SIZE: usize>(
    test_config: &TestConfig,
    full_node: FullNode,
    topology_override: Option<TopologyType>,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<(RelayerDriver, NaryConnectedChains<impl ChainHandle, SIZE>), Error> {
    let full_nodes = vec![full_node; SIZE];
    let (relayer, chains) = boostrap_chains_with_any_nodes(
        test_config,
        full_nodes,
        topology_override,
        config_modifier,
    )?;

    Ok((relayer, chains.try_into()?))
}

/**
   Bootstrap a dynamic number of chains, according to the number of full nodes
   in the `Vec<FullNode>`.
   The topology will be retrieved and set in this method,
   see [`crate::types::topology`] for more information.
*/
pub fn boostrap_chains_with_any_nodes(
    test_config: &TestConfig,
    full_nodes: Vec<FullNode>,
    topology_override: Option<TopologyType>,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<(RelayerDriver, DynamicConnectedChains<impl ChainHandle>), Error> {
    let mut config = Config::default();

    for (i, node) in full_nodes.iter().enumerate() {
        add_chain_config(&mut config, node, test_config, i)?;
    }

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let registry = new_registry(config.clone());

    let mut chain_handles = Vec::new();

    for node in full_nodes.iter() {
        let handle = spawn_chain_handle(&registry, node)?;
        chain_handles.push(handle);
    }

    // Retrieve the topology or fallback to the Linear topology
    let topology_type = if let Some(topology_type) = topology_override {
        topology_type
    } else {
        let topology_str = std::env::var("TOPOLOGY").unwrap_or_else(|_| "linear".to_owned());
        match topology_str.parse() {
            Ok(topology_type) => topology_type,
            Err(_) => {
                tracing::warn!(
                    "Failed to parse topology type `{topology_str}`. Will fallback to Linear topology"
                );
                TopologyType::Linear
            }
        }
    };
    let topology = bootstrap_topology(topology_type);

    let foreign_clients = topology.create_topology(&chain_handles)?;

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
