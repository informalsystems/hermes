use core::convert::TryInto;
use eyre::eyre;
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::sync::Arc;
use std::sync::RwLock;

use crate::bootstrap::binary::chain::{
    add_chain_config, add_keys_to_chain_handle, new_registry, save_relayer_config,
};
use crate::error::Error;
use crate::types::binary::chains::DropChainHandle;
use crate::types::config::TestConfig;
use crate::types::nary::chains::ConnectedChains;
use crate::types::single::node::FullNode;

pub fn boostrap_chains_with_nodes<const SIZE: usize>(
    test_config: &TestConfig,
    config_modifier: impl FnOnce(&mut Config),
    full_nodes: [FullNode; SIZE],
) -> Result<ConnectedChains<impl ChainHandle, SIZE>, Error> {
    let mut config = Config::default();

    for node in full_nodes.iter() {
        add_chain_config(&mut config, &node)?;
    }

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    let mut handles = Vec::new();

    for node in full_nodes.iter() {
        let handle = spawn_chain_handle(&registry, &node)?;
        handles.push(handle);
    }

    let mut foreign_clients_a: Vec<[ForeignClient<ProdChainHandle, ProdChainHandle>; SIZE]> =
        Vec::new();

    for handle_a in handles.iter() {
        let mut foreign_clients_b = Vec::new();

        for handle_b in handles.iter() {
            let foreign_client = ForeignClient::unsafe_new(handle_b.clone(), handle_a.clone())?;
            foreign_clients_b.push(foreign_client);
        }

        let array = foreign_clients_b.try_into().map_err(|_| {
            eyre!(
                "unexpected failure converting foreign clients vector into fixed size array {}",
                SIZE
            )
        })?;

        foreign_clients_a.push(array);
    }

    let foreign_clients = foreign_clients_a.try_into().map_err(|_| {
        eyre!(
            "unexpected failure converting foreign clients vector into fixed size array {}",
            SIZE
        )
    })?;

    let chain_handles = handles
        .into_iter()
        .map(DropChainHandle)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| {
            eyre!(
                "unexpected failure converting chain handles vector into fixed size array {}",
                SIZE
            )
        })?;

    let connected_chains = ConnectedChains {
        config_path,
        registry,
        chain_handles,
        full_nodes,
        foreign_clients,
    };

    Ok(connected_chains)
}

pub fn spawn_chain_handle(
    registry: &SharedRegistry<ProdChainHandle>,
    node: &FullNode,
) -> Result<ProdChainHandle, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry.get_or_spawn(chain_id)?;

    add_keys_to_chain_handle(&handle, &node.wallets)?;

    Ok(handle)
}
