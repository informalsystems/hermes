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
use tendermint_rpc::Url;
use tracing::info;

use crate::bootstrap::single::{bootstrap_single_chain, ChainService};
use crate::chain::builder::ChainBuilder;

pub struct ChainServices<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub config: config::Config,
    pub config_a: config::ChainConfig,
    pub config_b: config::ChainConfig,

    pub service_a: ChainService,
    pub service_b: ChainService,

    pub handle_a: ChainA,
    pub handle_b: ChainB,

    pub client_a_to_b: ForeignClient<ChainA, ChainB>,
    pub client_b_to_a: ForeignClient<ChainB, ChainA>,

    pub supervisor_cmd_sender: SupervisorCmdSender,
}

pub struct SupervisorCmdSender(pub Sender<SupervisorCmd>);

impl Drop for SupervisorCmdSender {
    fn drop(&mut self) {
        let _ = self.0.send(SupervisorCmd::Stop);
    }
}

pub fn boostrap_chain_pair(
    builder: &ChainBuilder,
) -> Result<ChainServices<impl ChainHandle, impl ChainHandle>, Error> {
    let service_a = bootstrap_single_chain(&builder)?;
    let service_b = bootstrap_single_chain(&builder)?;

    let config_a = create_chain_config(&service_a)?;
    let config_b = create_chain_config(&service_b)?;

    let mut config = config::Config::default();
    config.chains.push(config_a.clone());
    config.chains.push(config_b.clone());

    let config_str = toml::to_string_pretty(&config)?;

    info!("hermes config:\n{}", config_str);

    let (mut supervisor, supervisor_cmd_sender) =
        <Supervisor<ProdChainHandle>>::new(Arc::new(RwLock::new(config.clone())), None);

    let chain_id_a = service_a.chain.chain_id.clone();
    let chain_id_b = service_b.chain.chain_id.clone();

    let handle_a = supervisor.get_registry().get_or_spawn(&chain_id_a)?;
    let handle_b = supervisor.get_registry().get_or_spawn(&chain_id_b)?;

    std::thread::spawn(move || {
        supervisor.run().unwrap();
    });

    handle_a.add_key(
        service_a.relayer.id.0.clone(),
        service_a.relayer.key.clone(),
    )?;

    handle_a.add_key(service_a.user1.id.0.clone(), service_a.user1.key.clone())?;
    handle_a.add_key(service_a.user2.id.0.clone(), service_a.user2.key.clone())?;

    handle_b.add_key(
        service_b.relayer.id.0.clone(),
        service_b.relayer.key.clone(),
    )?;

    handle_b.add_key(service_b.user1.id.0.clone(), service_b.user1.key.clone())?;
    handle_b.add_key(service_b.user2.id.0.clone(), service_b.user2.key.clone())?;

    let client_a_to_b = ForeignClient::new(handle_b.clone(), handle_a.clone())?;
    let client_b_to_a = ForeignClient::new(handle_a.clone(), handle_b.clone())?;

    let res = ChainServices {
        config,
        config_a,
        config_b,

        service_a,
        service_b,

        handle_a,
        handle_b,

        client_a_to_b,
        client_b_to_a,

        supervisor_cmd_sender: SupervisorCmdSender(supervisor_cmd_sender),
    };

    Ok(res)
}

fn create_chain_config(chain: &ChainService) -> Result<config::ChainConfig, Error> {
    Ok(config::ChainConfig {
        id: chain.chain.chain_id.clone(),
        rpc_addr: Url::from_str(&chain.chain.rpc_address())?,
        websocket_addr: Url::from_str(&chain.chain.websocket_address())?,
        grpc_addr: Url::from_str(&chain.chain.grpc_address())?,
        rpc_timeout: Duration::from_secs(10),
        account_prefix: "cosmos".to_string(),
        key_name: chain.relayer.id.0.clone(),
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
