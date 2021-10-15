use core::str::FromStr;
use core::time::Duration;
use eyre::{eyre, Report as Error};
use ibc::application::ics20_fungible_token_transfer::derive_ibc_denom;
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChainId, PortId};
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::channel::Channel;
use ibc_relayer::config;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::Store;
use ibc_relayer::supervisor::{cmd::SupervisorCmd, Supervisor};
use ibc_relayer::transfer::{build_and_send_transfer_messages, Amount, TransferOptions};
use ibc_relayer_cli::cli_utils::ChainHandlePair;
use std::sync::Arc;
use std::sync::RwLock;
use tendermint_rpc::Url;
use tracing::info;

use crate::chain::bootstrap::{bootstrap_chain, wait_wallet_amount, BootstrapResult};
use crate::chain::builder::ChainBuilder;
use crate::init::init_test;

fn create_chain_config(chain: &BootstrapResult) -> Result<config::ChainConfig, Error> {
    Ok(config::ChainConfig {
        id: ChainId::from_string(&chain.chain.chain_id.0),
        rpc_addr: Url::from_str(&chain.chain.rpc_address())?,
        websocket_addr: Url::from_str(&chain.chain.websocket_address())?,
        grpc_addr: Url::from_str(&chain.chain.grpc_address())?,
        rpc_timeout: Duration::from_secs(10),
        account_prefix: "cosmos".to_string(),
        key_name: chain.relayer.id.0.clone(),
        key_store_type: Store::Test,
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

#[test]
fn test_chain_manager() -> Result<(), Error> {
    init_test()?;

    let builder = ChainBuilder::new("gaiad", "data");

    let chain_a = bootstrap_chain(&builder)?;
    let chain_b = bootstrap_chain(&builder)?;

    let chain_a_config = create_chain_config(&chain_a)?;
    let chain_b_config = create_chain_config(&chain_b)?;

    let mut config = config::Config::default();
    config.chains.push(chain_a_config.clone());
    config.chains.push(chain_b_config.clone());

    let config_str = toml::to_string_pretty(&config)?;

    info!("hermes config:\n{}", config_str);

    let chain_handles = ChainHandlePair::spawn(
        &config,
        &ChainId::from_string(&chain_a.chain.chain_id.0),
        &&ChainId::from_string(&chain_b.chain.chain_id.0),
    )?;

    info!(
        "adding key {} to chain config {} with key entry {:?}",
        chain_a.relayer.id.0,
        chain_handles.src.id(),
        chain_a.relayer.key,
    );

    chain_handles
        .src
        .add_key(chain_a.relayer.id.0.clone(), chain_a.relayer.key.clone())?;

    chain_handles
        .src
        .add_key(chain_a.user.id.0.clone(), chain_a.user.key.clone())?;

    chain_handles
        .dst
        .add_key(chain_b.relayer.id.0.clone(), chain_b.relayer.key.clone())?;

    chain_handles
        .dst
        .add_key(chain_b.user.id.0.clone(), chain_b.user.key.clone())?;

    let client_a_to_b = ForeignClient::new(chain_handles.dst.clone(), chain_handles.src.clone())?;

    let client_b_to_a = ForeignClient::new(chain_handles.src.clone(), chain_handles.dst.clone())?;

    let connection = Connection::new(
        client_a_to_b.clone(),
        client_b_to_a.clone(),
        default::connection_delay(),
    )?;

    let transfer_port = PortId::from_str("transfer")?;

    let channel = Channel::new(
        connection,
        Order::Unordered,
        transfer_port.clone(),
        transfer_port.clone(),
        None,
    )?;

    info!("created new channel {:?}", channel);

    // let res = client_a_to_b.build_create_client_and_send()?;
    // info!("created client: {}", res);

    let channel_id_a = channel
        .a_side
        .channel_id()
        .ok_or_else(|| eyre!("expect channel id"))?;

    let channel_id_b = channel
        .b_side
        .channel_id()
        .ok_or_else(|| eyre!("expect channel id"))?;

    let transfer_options = TransferOptions {
        packet_src_chain_config: chain_a_config,
        packet_dst_chain_config: chain_b_config,
        packet_src_port_id: transfer_port.clone(),
        packet_src_channel_id: channel_id_a.clone(),
        amount: Amount(1000_000.into()),
        denom: "samoleans".to_string(),
        receiver: Some(chain_b.user.address.0.clone()),
        timeout_height_offset: 100,
        timeout_seconds: Duration::from_secs(0),
        number_msgs: 1,
    };

    let (supervisor, supervisor_sender) =
        <Supervisor<ProdChainHandle>>::new(Arc::new(RwLock::new(config.clone())), None);

    std::thread::spawn(move || {
        supervisor.run().unwrap();
    });

    info!("Sending IBC transfer");

    let res =
        build_and_send_transfer_messages(chain_handles.src, chain_handles.dst, transfer_options)?;

    info!("IBC transfer result: {:?}", res);

    let denom_b = derive_ibc_denom(&transfer_port, &channel_id_b, "samoleans")?;

    info!(
        "Waiting for user on chain B to receive transfer in denom {}",
        denom_b
    );

    wait_wallet_amount(&chain_b.chain, &chain_b.user, 1_000_000, &denom_b, 20)?;

    info!("successfully performed IBC transfer");

    supervisor_sender.send(SupervisorCmd::Stop)?;

    std::thread::sleep(Duration::from_secs(1));

    Ok(())
}
