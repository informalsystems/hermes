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
use crate::chain::cli::provider::{jq_exp, query_consumer_genesis};
use crate::chain::config;
use crate::chain::exec::simple_exec;
use crate::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use crate::error::Error;
use crate::prelude::{ChainDriver, Denom, FullNode, TestWallets, Token};
use crate::types::wallet::Wallet;
use crate::util::random::{random_u128_range, random_u32};

pub fn bootstrap_consumer_node(
    builder: &ChainBuilder,
    prefix: &str,
    node_a: &FullNode,
    config_modifier: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    genesis_modifier: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    chain_number: usize,
    provider_chain_driver: &ChainDriver,
) -> Result<FullNode, Error> {
    let stake_denom = Denom::base("stake");

    let denom = Denom::base("samoleans");

    let initial_amount = random_u128_range(1_000_000_000_000_000_000, 2_000_000_000_000_000_000);

    let initial_stake = Token::new(stake_denom, initial_amount);
    let additional_initial_stake = initial_stake
        .clone()
        .checked_add(1_000_000_000_000u64)
        .ok_or(Error::generic(eyre!(
            "error creating initial stake with additional amount"
        )))?;

    let initial_coin = Token::new(denom.clone(), initial_amount);
    let chain_driver = builder.new_chain(prefix, false, chain_number)?;

    chain_driver.initialize()?;

    let validator = add_wallet(&chain_driver, "validator", false)?;
    let relayer = add_wallet(&chain_driver, "relayer", false)?;
    let user1 = add_wallet(&chain_driver, "user1", false)?;
    let user2 = add_wallet(&chain_driver, "user2", false)?;

    chain_driver.add_genesis_account(&validator.address, &[&additional_initial_stake])?;
    chain_driver.add_genesis_account(&relayer.address, &[&initial_stake, &initial_coin])?;
    chain_driver.add_genesis_account(&user1.address, &[&initial_stake, &initial_coin])?;
    chain_driver.add_genesis_account(&user2.address, &[&initial_stake, &initial_coin])?;

    // Wait for the consumer chain to be initialized before querying the genesis
    thread::sleep(Duration::from_secs(10));

    query_consumer_genesis(
        &chain_driver,
        node_a.chain_driver.chain_id.as_str(),
        &node_a.chain_driver.command_path,
        &node_a.chain_driver.home_path,
        &node_a.chain_driver.rpc_listen_address(),
        chain_driver.chain_id.as_str(),
    )?;

    jq_exp(
        &chain_driver,
        &chain_driver.home_path,
        node_a.chain_driver.chain_id.as_str(),
    )?;

    chain_driver.update_genesis_file("genesis.json", genesis_modifier)?;

    let log_level = std::env::var("CHAIN_LOG_LEVEL").unwrap_or_else(|_| "info".to_string());

    chain_driver.update_chain_config("config.toml", |config| {
        config::set_log_level(config, &log_level)?;
        config::set_rpc_port(config, chain_driver.rpc_port)?;
        config::set_p2p_port(config, chain_driver.p2p_port)?;
        config::set_pprof_port(config, chain_driver.pprof_port)?;
        config::set_timeout_commit(config, Duration::from_secs(1))?;
        config::set_timeout_propose(config, Duration::from_secs(1))?;
        config::set_mode(config, "validator")?;

        config_modifier(config)?;

        Ok(())
    })?;

    chain_driver.update_chain_config("app.toml", |config| {
        config::set_grpc_port(config, chain_driver.grpc_port)?;
        config::disable_grpc_web(config)?;
        config::disable_api(config)?;
        config::set_minimum_gas_price(config, "0stake")?;

        Ok(())
    })?;

    simple_exec(
        chain_driver.chain_id.as_str(),
        "cp",
        &[
            &format!(
                "{}/config/priv_validator_key.json",
                provider_chain_driver.home_path
            ),
            &format!("{}/config/priv_validator_key.json", chain_driver.home_path),
        ],
    )?;

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

fn add_wallet(driver: &ChainDriver, prefix: &str, use_random_id: bool) -> Result<Wallet, Error> {
    if use_random_id {
        let num = random_u32();
        let wallet_id = format!("{prefix}-{num:x}");
        driver.add_wallet(&wallet_id)
    } else {
        driver.add_wallet(prefix)
    }
}
