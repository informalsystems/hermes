/*!
    Helper functions for bootstrapping two relayer chain handles
    with connected foreign clients.
*/
use eyre::Report as Error;
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::{Config, SharedConfig};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use std::fs;
use std::sync::Arc;
use std::sync::RwLock;
use tracing::info;

use crate::tagged::*;
use crate::types::binary::chains::ConnectedChains;
use crate::types::config::TestConfig;
use crate::types::single::client_server::ChainClientServer;
use crate::types::single::node::FullNode;
use crate::types::wallet::{ChainWallets, Wallet};
use crate::util::random::random_u32;

/**
   Bootstraps two relayer chain handles with connected foreign clients.

   Takes two [`FullNode`] values representing two different running
   full nodes, and return a [`ConnectedChains`] that contain the given
   full nodes together with the corresponding two [`ChainHandle`]s and
   [`ForeignClient`]s. Also accepts an [`FnOnce`] closure that modifies
   the relayer's [`Config`] before the chain handles are initialized.
*/
pub fn boostrap_chain_pair_with_nodes(
    test_config: &TestConfig,
    node_a: FullNode,
    node_b: FullNode,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ConnectedChains<impl ChainHandle, impl ChainHandle>, Error> {
    let mut config = Config::default();

    add_chain_config(&mut config, &node_a)?;
    add_chain_config(&mut config, &node_b)?;

    config_modifier(&mut config);

    let config_str = toml::to_string_pretty(&config)?;

    let config_path = test_config
        .chain_store_dir
        .join(format!("config-{:x}.toml", random_u32()));

    fs::write(&config_path, &config_str)?;

    info!(
        "written hermes config.toml to {}:\n{}",
        config_path.display(),
        config_str
    );

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    let side_a = spawn_chain_handle(|| {}, &registry, node_a)?;
    let side_b = spawn_chain_handle(|| {}, &registry, node_b)?;

    let client_a_to_b = ForeignClient::new(side_b.handle.clone(), side_a.handle.clone())?;
    let client_b_to_a = ForeignClient::new(side_a.handle.clone(), side_b.handle.clone())?;

    Ok(ConnectedChains {
        config,
        config_path,
        registry,
        client_a_to_b,
        client_b_to_a,
        side_a,
        side_b,
    })
}

fn add_key_to_chain_handle<Chain: ChainHandle>(
    chain: &Chain,
    wallet: &MonoTagged<Chain, &Wallet>,
) -> Result<(), Error> {
    chain.add_key(wallet.value().id.0.clone(), wallet.value().key.clone())?;

    Ok(())
}

fn add_keys_to_chain_handle<Chain: ChainHandle>(
    chain: &Chain,
    wallets: &MonoTagged<Chain, &ChainWallets>,
) -> Result<(), Error> {
    add_key_to_chain_handle(chain, &wallets.relayer())?;
    add_key_to_chain_handle(chain, &wallets.user1())?;
    add_key_to_chain_handle(chain, &wallets.user2())?;

    Ok(())
}

fn new_registry(config: SharedConfig) -> SharedRegistry<ProdChainHandle> {
    <SharedRegistry<ProdChainHandle>>::new(config)
}

fn add_chain_config(config: &mut Config, running_node: &FullNode) -> Result<(), Error> {
    let chain_config = running_node.generate_chain_config()?;

    config.chains.push(chain_config);
    Ok(())
}

fn spawn_chain_handle(
    _: impl Tag,
    registry: &SharedRegistry<impl ChainHandle + 'static>,
    node: FullNode,
) -> Result<ChainClientServer<impl ChainHandle>, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry.get_or_spawn(chain_id)?;
    let node = MonoTagged::new(node);

    add_keys_to_chain_handle(&handle, &node.wallets())?;

    Ok(ChainClientServer::new(handle, node))
}
