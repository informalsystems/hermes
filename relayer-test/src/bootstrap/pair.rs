use eyre::Report as Error;

use core::str::FromStr;
use core::time::Duration;
use crossbeam_channel::Sender;
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::Store;
use ibc_relayer::supervisor::{cmd::SupervisorCmd, Supervisor};
use std::sync::Arc;
use std::sync::RwLock;
use std::thread;
use tendermint_rpc::Url;
use tracing::info;

use crate::bootstrap::single::{bootstrap_single_chain, ChainDeployment as SingleDeployment};
use crate::chain::builder::ChainBuilder;
use crate::chain::wallet::Wallet;
use crate::tagged::mono::Tagged as MonoTagged;

use super::wallets::ChainWallets;

pub struct ChainsDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    // Have this as first field to drop the supervisor
    // first before stopping the chain driver.
    pub supervisor_cmd_sender: SupervisorCmdSender,

    pub config: config::Config,

    pub side_a: ChainDeployment<ChainA, ChainB>,
    pub side_b: ChainDeployment<ChainB, ChainA>,
}

pub struct ChainDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub config: config::ChainConfig,

    pub handle: ChainA,

    pub foreign_client: ForeignClient<ChainA, ChainB>,

    pub server: MonoTagged<ChainA, SingleDeployment>,
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

pub fn boostrap_chain_pair(
    builder: &ChainBuilder,
) -> Result<ChainsDeployment<impl ChainHandle, impl ChainHandle>, Error> {
    let service_a = bootstrap_single_chain(&builder)?;
    let service_b = bootstrap_single_chain(&builder)?;

    let config_a = create_chain_config(service_a.value())?;
    let config_b = create_chain_config(service_b.value())?;

    let mut config = config::Config::default();

    config.chains.push(config_a.clone());
    config.chains.push(config_b.clone());

    let config_str = toml::to_string_pretty(&config)?;

    info!("hermes config:\n{}", config_str);

    let (mut supervisor, supervisor_cmd_sender) =
        <Supervisor<ProdChainHandle>>::new(Arc::new(RwLock::new(config.clone())), None);

    let chain_id_a = service_a.value().chain_driver.chain_id.clone();
    let chain_id_b = service_b.value().chain_driver.chain_id.clone();

    let handle_a = supervisor.get_registry().get_or_spawn(&chain_id_a)?;
    let handle_b = supervisor.get_registry().get_or_spawn(&chain_id_b)?;

    std::thread::spawn(move || {
        supervisor.run().unwrap();
    });

    let service_a = service_a.retag();
    let service_b = service_b.retag();

    add_keys_to_chain_handle(&handle_a, &service_a.wallets())?;
    add_keys_to_chain_handle(&handle_b, &service_b.wallets())?;

    let client_a_to_b = ForeignClient::new(handle_b.clone(), handle_a.clone())?;
    let client_b_to_a = ForeignClient::new(handle_a.clone(), handle_b.clone())?;

    Ok(ChainsDeployment {
        supervisor_cmd_sender: SupervisorCmdSender(supervisor_cmd_sender),

        config,

        side_a: ChainDeployment {
            config: config_a,

            handle: handle_a,

            foreign_client: client_a_to_b,

            server: service_a,
        },

        side_b: ChainDeployment {
            config: config_b,

            handle: handle_b,

            foreign_client: client_b_to_a,

            server: service_b,
        },
    })
}

fn create_chain_config(chain: &SingleDeployment) -> Result<config::ChainConfig, Error> {
    Ok(config::ChainConfig {
        id: chain.chain_driver.chain_id.clone(),
        rpc_addr: Url::from_str(&chain.chain_driver.rpc_address())?,
        websocket_addr: Url::from_str(&chain.chain_driver.websocket_address())?,
        grpc_addr: Url::from_str(&chain.chain_driver.grpc_address())?,
        rpc_timeout: Duration::from_secs(10),
        account_prefix: "cosmos".to_string(),
        key_name: chain.wallets.relayer.id.0.clone(),
        key_store_type: Store::Memory,
        store_prefix: "ibc".to_string(),
        default_gas: None,
        max_gas: Some(3000000),
        gas_adjustment: Some(0.1),
        max_msg_num: Default::default(),
        max_tx_size: Default::default(),
        clock_drift: Duration::from_secs(5),
        trusting_period: Some(Duration::from_secs(14 * 24 * 3600)),
        trust_threshold: Default::default(),
        gas_price: config::GasPrice::new(0.001, "stake".to_string()),
        packet_filter: Default::default(),
        address_type: Default::default(),
        memo_prefix: Default::default(),
    })
}
