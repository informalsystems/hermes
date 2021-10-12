use core::str::FromStr;
use core::time::Duration;
use eyre::Report as Error;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::Store;
use ibc_relayer_cli::cli_utils::ChainHandlePair;
use tendermint_rpc::Url;
use tracing::info;

use crate::chain::bootstrap::{bootstrap_chain, BootstrapResult};
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
    config.chains.push(chain_a_config);
    config.chains.push(chain_b_config);

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
        .add_key(chain_a.relayer.id.0.clone(), chain_a.relayer.key)?;

    chain_handles
        .dst
        .add_key(chain_b.relayer.id.0.clone(), chain_b.relayer.key)?;

    let client = ForeignClient::restore(ClientId::default(), chain_handles.dst, chain_handles.src);

    let res = client.build_create_client_and_send()?;

    info!("successfully created client: {}", res);

    Ok(())
}
