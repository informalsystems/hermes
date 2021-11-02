use eyre::Report as Error;

use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::supervisor::Supervisor;
use std::sync::Arc;
use std::sync::RwLock;
use tracing::info;

use crate::bootstrap::single::bootstrap_single_chain;
use crate::chain::builder::ChainBuilder;
use crate::tagged::*;
use crate::types::wallet::Wallet;

use crate::types::binary::chains::{ChainDeployment, SupervisorCmdSender};
use crate::types::single::client_server::ChainClientServer;
use crate::types::single::node::RunningNode;
use crate::types::wallets::ChainWallets;

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

fn spawn_supervisor(config: &Config) -> (Supervisor<impl ChainHandle>, SupervisorCmdSender) {
    let (supervisor, sender) =
        <Supervisor<ProdChainHandle>>::new(Arc::new(RwLock::new(config.clone())), None);

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
    supervisor: &mut Supervisor<impl ChainHandle + 'static>,
    node: MonoTagged<impl Tag, RunningNode>,
) -> Result<ChainClientServer<impl ChainHandle>, Error> {
    let chain_id = node.chain_id();
    let handle = supervisor.get_registry().get_or_spawn(chain_id.value())?;
    let node = node.retag();

    add_keys_to_chain_handle(&handle, &node.wallets())?;

    Ok(ChainClientServer::new(handle, node))
}

pub fn boostrap_chain_pair(
    builder: &ChainBuilder,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ChainDeployment<impl ChainHandle, impl ChainHandle>, Error> {
    let node_a = bootstrap_single_chain(&builder)?;
    let node_b = bootstrap_single_chain(&builder)?;

    let mut config = Config::default();

    add_chain_config(&mut config, node_a.value())?;
    add_chain_config(&mut config, node_b.value())?;

    config_modifier(&mut config);

    let config_str = toml::to_string_pretty(&config)?;

    info!("hermes config:\n{}", config_str);

    let (mut supervisor, supervisor_cmd_sender) = spawn_supervisor(&config);

    let side_a = spawn_chain_handle(|| {}, &mut supervisor, node_a)?;
    let side_b = spawn_chain_handle(|| {}, &mut supervisor, node_b)?;

    run_supervisor(supervisor);

    let client_a_to_b = ForeignClient::new(side_b.handle.clone(), side_a.handle.clone())?;
    let client_b_to_a = ForeignClient::new(side_a.handle.clone(), side_b.handle.clone())?;

    Ok(ChainDeployment {
        supervisor_cmd_sender,
        config,
        client_a_to_b,
        client_b_to_a,
        side_a,
        side_b,
    })
}
