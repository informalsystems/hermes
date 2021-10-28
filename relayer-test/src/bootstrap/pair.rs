use eyre::Report as Error;

use core::time::Duration;
use crossbeam_channel::Sender;
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::supervisor::{cmd::SupervisorCmd, Supervisor};
use std::sync::Arc;
use std::sync::RwLock;
use std::thread;
use tracing::info;

use crate::bootstrap::single::bootstrap_single_chain;
use crate::chain::builder::ChainBuilder;
use crate::chain::wallet::Wallet;
use crate::tagged::*;

use super::client_server::ChainClientServer;
use super::running_node::RunningNode;
use super::wallets::ChainWallets;

pub struct ChainsDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    // Have this as first field to drop the supervisor
    // first before stopping the chain driver.
    pub supervisor_cmd_sender: SupervisorCmdSender,

    pub config: Config,

    pub client_a_to_b: ForeignClient<ChainB, ChainA>,

    pub client_b_to_a: ForeignClient<ChainA, ChainB>,

    pub side_a: ChainClientServer<ChainA>,
    pub side_b: ChainClientServer<ChainB>,
}

// A wrapper around the SupervisorCmd sender so that we can
// send stop signal to the supervisor before stopping the
// chain drivers to prevent the supervisor from raising
// errors caused by closed connections.
pub struct SupervisorCmdSender(pub Sender<SupervisorCmd>);

impl Drop for SupervisorCmdSender {
    fn drop(&mut self) {
        let _ = self.0.send(SupervisorCmd::Stop);
        thread::sleep(Duration::from_millis(1000));
    }
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

fn spawn_supervisor(config: &Config) -> (Supervisor<impl ChainHandle>, SupervisorCmdSender) {
    let (supervisor, sender) =
        <Supervisor<ProdChainHandle>>::new(Arc::new(RwLock::new(config.clone())), None);

    (supervisor, SupervisorCmdSender(sender))
}

fn add_chain_config(config: &mut Config, running_node: &RunningNode) -> Result<(), Error> {
    let chain_config = running_node.generate_chain_config()?;

    config.chains.push(chain_config);
    Ok(())
}

fn run_supervisor(mut supervisor: Supervisor<impl ChainHandle + 'static>) {
    std::thread::spawn(move || {
        supervisor.run().unwrap();
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
) -> Result<ChainsDeployment<impl ChainHandle, impl ChainHandle>, Error> {
    let node_a = bootstrap_single_chain(&builder)?;
    let node_b = bootstrap_single_chain(&builder)?;

    let mut config = Config::default();

    add_chain_config(&mut config, node_a.value())?;
    add_chain_config(&mut config, node_b.value())?;

    let config_str = toml::to_string_pretty(&config)?;

    info!("hermes config:\n{}", config_str);

    let (mut supervisor, supervisor_cmd_sender) = spawn_supervisor(&config);

    let side_a = spawn_chain_handle(|| {}, &mut supervisor, node_a)?;
    let side_b = spawn_chain_handle(|| {}, &mut supervisor, node_b)?;

    run_supervisor(supervisor);

    let client_a_to_b = ForeignClient::new(side_b.handle.clone(), side_a.handle.clone())?;
    let client_b_to_a = ForeignClient::new(side_a.handle.clone(), side_b.handle.clone())?;

    Ok(ChainsDeployment {
        supervisor_cmd_sender,

        config,

        client_a_to_b,

        client_b_to_a,

        side_a,

        side_b,
    })
}
