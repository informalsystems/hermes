use core::time::Duration;
use tracing::info;

use crate::chain::builder::ChainBuilder;
use crate::chain::config;
use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::tagged::mono::Tagged as MonoTagged;
use crate::tagged::tag::Tag;
use crate::util::random::{random_u32, random_u64_range};

use super::running_node::RunningNode;
use super::wallets::ChainWallets;

pub fn bootstrap_single_chain(
    builder: &ChainBuilder,
) -> Result<MonoTagged<impl Tag, RunningNode>, Error> {
    let stake_denom = Denom("stake".to_string());
    let denom = Denom(format!("coin{:x}", random_u32()));
    let initial_amount = random_u64_range(1_000_000_000_000, 9_000_000_000_000);

    let chain_driver = builder.new_chain();

    info!("created new chain: {}", chain_driver.chain_id);

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

    chain_driver.update_chain_config(|config| {
        config::set_log_level(config, &log_level)?;
        config::set_rpc_port(config, chain_driver.rpc_port)?;
        config::set_p2p_port(config, chain_driver.p2p_port)?;
        config::set_timeout_commit(config, Duration::from_secs(1))?;
        config::set_timeout_propose(config, Duration::from_secs(1))?;

        Ok(())
    })?;

    let chain_process = chain_driver.start()?;

    let wallets = ChainWallets {
        validator,
        relayer,
        user1,
        user2,
    };

    let deployment = <MonoTagged<(), _>>::new(RunningNode {
        chain_driver,
        chain_process,
        denom,
        wallets,
    });

    deployment.chain_driver().assert_eventual_wallet_amount(
        &deployment.wallets().relayer(),
        initial_amount,
        &deployment.denom(),
    )?;

    Ok(deployment)
}
