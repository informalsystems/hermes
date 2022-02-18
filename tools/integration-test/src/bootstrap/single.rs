/*!
   Helper functions for bootstrapping a single full node.
*/
use core::time::Duration;
use std::sync::{Arc, RwLock};
use toml;
use tracing::info;

use crate::chain::builder::ChainBuilder;
use crate::chain::config;
use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::types::single::node::FullNode;
use crate::types::wallet::TestWallets;
use crate::util::random::{random_u32, random_u64_range};

/**
   Bootstrap a single full node with the provided [`ChainBuilder`] and
   a prefix for the chain ID.

   The function would generate random postfix attached to the end of
   a chain ID. So for example having a prefix `"alpha"` may generate
   a chain with an ID  like `"ibc-alpha-f5a2a988"`

   The bootstrap function also tries to use as many random parameters
   when intitializing the chain, such as using random denomination
   and wallets. This is to help ensure that the test is written to
   only work with specific hardcoded parameters.

   TODO: Due to the limitation of the `gaiad` command, currently
   parameters such as the stake denomination (`stake`) and the wallet
   address prefix (`cosmos`) cannot be overridden. It would be
   great to be able to randomize these parameters in the future
   as well.
*/
pub fn bootstrap_single_node(
    builder: &ChainBuilder,
    prefix: &str,
    config_modifier: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
) -> Result<FullNode, Error> {
    let stake_denom = Denom::base("stake");
    let denom = Denom::base(&format!("coin{:x}", random_u32()));
    let initial_amount = random_u64_range(1_000_000_000_000, 9_000_000_000_000);

    let chain_driver = builder.new_chain(prefix)?;

    chain_driver.initialize()?;

    let validator = chain_driver.add_random_wallet("validator")?;
    let relayer = chain_driver.add_random_wallet("relayer")?;
    let user1 = chain_driver.add_random_wallet("user1")?;
    let user2 = chain_driver.add_random_wallet("user2")?;

    chain_driver.add_genesis_account(&validator.address, &[(&stake_denom, initial_amount)])?;

    chain_driver.add_genesis_validator(&validator.id, &stake_denom, initial_amount)?;

    chain_driver.add_genesis_account(
        &user1.address,
        &[(&stake_denom, initial_amount), (&denom, initial_amount)],
    )?;

    chain_driver.add_genesis_account(
        &user2.address,
        &[(&stake_denom, initial_amount), (&denom, initial_amount)],
    )?;

    chain_driver.add_genesis_account(
        &relayer.address,
        &[(&stake_denom, initial_amount), (&denom, initial_amount)],
    )?;

    chain_driver.collect_gen_txs()?;

    let log_level = std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string());

    chain_driver.update_chain_config("config.toml", |config| {
        config::set_log_level(config, &log_level)?;
        config::set_rpc_port(config, chain_driver.rpc_port)?;
        config::set_p2p_port(config, chain_driver.p2p_port)?;
        config::set_timeout_commit(config, Duration::from_secs(1))?;
        config::set_timeout_propose(config, Duration::from_secs(1))?;

        config_modifier(config)?;

        Ok(())
    })?;

    let process = chain_driver.start()?;

    chain_driver.assert_eventual_wallet_amount(&relayer, initial_amount, &denom)?;

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
