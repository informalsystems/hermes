/*!
Helper functions for bootstrapping a consumer full node.
*/
use eyre::eyre;
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::Duration;
use toml;
use tracing::info;

use crate::chain::builder::ChainBuilder;
use crate::chain::cli::provider::validator_opt_in;
use crate::chain::config;
use crate::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use crate::error::Error;
use crate::prelude::{ChainDriver, Denom, FullNode, TestWallets, Token};
use crate::util::random::random_u128_range;

pub fn bootstrap_consumer_node(
    builder: &ChainBuilder,
    prefix: &str,
    node_a: &FullNode,
    config_modifier: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    genesis_modifier: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    chain_number: usize,
    provider_chain_driver: &ChainDriver,
    provider_fee: &String,
) -> Result<FullNode, Error> {
    let stake_denom = Denom::base("stake", "stake");

    let denom = Denom::base("samoleans", "samoleans");

    let initial_amount = random_u128_range(1_000_000_000_000_000_000, 2_000_000_000_000_000_000);

    let initial_stake = Token::new(stake_denom, initial_amount);
    let additional_initial_stake = initial_stake
        .clone()
        .checked_add(1_000_000_000_000u64)
        .ok_or(Error::generic(eyre!(
            "error creating initial stake with additional amount"
        )))?;

    let initial_coin = Token::new(denom.clone(), initial_amount);
    let chain_driver = builder.new_chain("consumer", false, chain_number)?;

    chain_driver.initialize()?;

    let validator = chain_driver.add_wallet("validator")?;
    let relayer = chain_driver.add_wallet("relayer")?;
    let user1 = chain_driver.add_wallet("user1")?;
    let user2 = chain_driver.add_wallet("user2")?;

    chain_driver.add_genesis_account(&validator.address, &[&additional_initial_stake])?;
    chain_driver.add_genesis_account(&relayer.address, &[&initial_stake, &initial_coin])?;
    chain_driver.add_genesis_account(&user1.address, &[&initial_stake, &initial_coin])?;
    chain_driver.add_genesis_account(&user2.address, &[&initial_stake, &initial_coin])?;

    // Wait for the consumer chain to be initialized before querying the genesis
    thread::sleep(Duration::from_secs(5));

    validator_opt_in(
        provider_chain_driver.chain_id.as_str(),
        &provider_chain_driver.command_path,
        &provider_chain_driver.home_path,
        &provider_chain_driver.rpc_listen_address(),
        provider_fee,
        prefix,
    )?;

    // Wait enough time so that the spawn_time passed
    thread::sleep(Duration::from_secs(30));

    node_a
        .chain_driver
        .query_consumer_genesis(&chain_driver, prefix)?;

    chain_driver.replace_genesis_state()?;

    chain_driver.update_genesis_file("genesis.json", genesis_modifier)?;
    // The configuration `soft_opt_out_threshold` might be missing and is required
    // for chains such as Neutron
    let globalfee_minimum_gas = serde_json::json!([
        {
            "denom": "stake",
            "amount": "0",
        }
    ]);
    chain_driver.update_genesis_file("genesis.json", |genesis| {
        config::cosmos::set_soft_opt_out_threshold(genesis, "0.05")?;
        config::cosmos::consensus_params_max_gas(genesis, "3000000")?;
        config::cosmos::globalfee_minimum_gas_prices(genesis, globalfee_minimum_gas)?;
        config::cosmos::set_retry_delay_period(genesis, "100s")?;
        Ok(())
    })?;

    let log_level = std::env::var("CHAIN_LOG_LEVEL").unwrap_or_else(|_| "info".to_string());

    chain_driver.update_chain_config("config/config.toml", |config| {
        config::cosmos::set_log_level(config, &log_level)?;
        config::cosmos::set_rpc_port(config, chain_driver.rpc_port)?;
        config::cosmos::set_p2p_port(config, chain_driver.p2p_port)?;
        config::cosmos::set_pprof_port(config, chain_driver.pprof_port)?;
        config::cosmos::set_timeout_commit(config, Duration::from_secs(1))?;
        config::cosmos::set_timeout_propose(config, Duration::from_secs(1))?;
        config::cosmos::set_mode(config, "validator")?;

        config_modifier(config)?;

        Ok(())
    })?;

    chain_driver.update_chain_config("config/app.toml", |config| {
        config::cosmos::set_grpc_port(config, chain_driver.grpc_port)?;
        config::cosmos::disable_grpc_web(config)?;
        config::cosmos::disable_api(config)?;
        config::cosmos::set_minimum_gas_price(config, "0stake")?;

        Ok(())
    })?;

    chain_driver.copy_validator_key_pair(provider_chain_driver)?;

    let process = chain_driver.start()?;

    info!(
        "started new chain {} at with home path {} and RPC address {}.",
        chain_driver.chain_id,
        chain_driver.home_path,
        chain_driver.rpc_address(),
    );

    info!(
        "user wallet for chain {} - id: {}, address: {}",
        chain_driver.chain_id, user1.id.0, user1.address.0,
    );

    info!(
        "you can manually interact with the chain using commands starting with:\n{} --home '{}' --node {}",
        chain_driver.command_path,
        chain_driver.home_path,
        chain_driver.rpc_address(),
    );

    let wallets = TestWallets {
        validator,
        relayer,
        user1,
        user2,
    };

    let node = FullNode {
        chain_driver,
        denom,
        wallets,
        process: Arc::new(RwLock::new(process)),
    };

    Ok(node)
}
