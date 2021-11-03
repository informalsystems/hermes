use eyre::Report as Error;

use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::{Config, SharedConfig};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer::supervisor::Supervisor;
use std::sync::Arc;
use std::sync::RwLock;
use tracing::info;

use crate::tagged::*;
use crate::types::binary::chains::{ConnectedChains, SupervisorCmdSender};
use crate::types::single::client_server::ChainClientServer;
use crate::types::single::node::RunningNode;
use crate::types::wallet::Wallet;
use crate::types::wallets::ChainWallets;

pub fn boostrap_chain_pair_with_nodes(
    node_a: RunningNode,
    node_b: RunningNode,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ConnectedChains<impl ChainHandle, impl ChainHandle>, Error> {
    let mut config = Config::default();

    add_chain_config(&mut config, &node_a)?;
    add_chain_config(&mut config, &node_b)?;

    config_modifier(&mut config);

    let config_str = toml::to_string_pretty(&config)?;

    info!("hermes config:\n{}", config_str);

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    let (supervisor, supervisor_cmd_sender) = spawn_supervisor(config.clone(), registry.clone());

    let side_a = spawn_chain_handle(|| {}, &registry, node_a)?;
    let side_b = spawn_chain_handle(|| {}, &registry, node_b)?;

    run_supervisor(supervisor);

    let client_a_to_b = ForeignClient::new(side_b.handle.clone(), side_a.handle.clone())?;
    let client_b_to_a = ForeignClient::new(side_a.handle.clone(), side_b.handle.clone())?;

    Ok(ConnectedChains {
        supervisor_cmd_sender,
        config,
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

fn new_registry(config: SharedConfig) -> SharedRegistry<impl ChainHandle + 'static> {
    <SharedRegistry<ProdChainHandle>>::new(config)
}

fn spawn_supervisor(
    config: SharedConfig,
    registry: SharedRegistry<impl ChainHandle + 'static>,
) -> (Supervisor<impl ChainHandle>, SupervisorCmdSender) {
    let (supervisor, sender) = Supervisor::new_with_registry(config, registry, None);

    (supervisor, SupervisorCmdSender::new(sender))
}

fn add_chain_config(config: &mut Config, running_node: &RunningNode) -> Result<(), Error> {
    let chain_config = running_node.generate_chain_config()?;

    config.chains.push(chain_config);
    Ok(())
}

fn run_supervisor(mut supervisor: Supervisor<impl ChainHandle + 'static>) {
    std::thread::spawn(move || {
        supervisor.run_without_health_check().unwrap();
    });
}

fn spawn_chain_handle(
    _: impl Tag,
    registry: &SharedRegistry<impl ChainHandle + 'static>,
    node: RunningNode,
) -> Result<ChainClientServer<impl ChainHandle>, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry.get_or_spawn(chain_id)?;
    let node = MonoTagged::new(node);

    add_keys_to_chain_handle(&handle, &node.wallets())?;

    Ok(ChainClientServer::new(handle, node))
}
