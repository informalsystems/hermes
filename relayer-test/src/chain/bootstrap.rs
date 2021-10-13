use core::time::Duration;
use eyre::{eyre, Report as Error};
use std::thread;
use tracing::{debug, info, trace};

use super::builder::ChainBuilder;
use super::command::ChainCommand;
use super::config;
use super::wallet::Wallet;
use crate::process::ChildProcess;

pub struct BootstrapResult {
    pub chain: ChainCommand,
    pub process: ChildProcess,
    pub validator: Wallet,
    pub relayer: Wallet,
    pub user: Wallet,
}

pub fn bootstrap_chain(builder: &ChainBuilder) -> Result<BootstrapResult, Error> {
    const COIN_AMOUNT: u64 = 1_000_000_000_000;

    let chain = builder.new_chain();

    info!("created new chain: {:?}", chain);

    chain.initialize()?;

    let validator = chain.add_random_wallet("validator")?;
    let user = chain.add_random_wallet("user")?;
    let relayer = chain.add_random_wallet("relayer")?;

    chain.add_genesis_account(&validator.address, &[("stake", COIN_AMOUNT)])?;

    chain.add_genesis_validator(&validator.id, "stake", 1_000_000_000_000)?;

    chain.add_genesis_account(
        &user.address,
        &[("stake", COIN_AMOUNT), ("samoleans", COIN_AMOUNT)],
    )?;

    chain.add_genesis_account(
        &relayer.address,
        &[("stake", COIN_AMOUNT), ("samoleans", COIN_AMOUNT)],
    )?;

    chain.collect_gen_txs()?;

    chain.update_chain_config(|config| {
        config::set_log_level(config, "trace")?;
        config::set_rpc_port(config, chain.rpc_port)?;
        config::set_p2p_port(config, chain.p2p_port)?;
        config::set_timeout_commit(config, Duration::from_secs(1))?;
        config::set_timeout_propose(config, Duration::from_secs(1))?;

        Ok(())
    })?;

    let process = chain.start()?;

    wait_wallet_amount(&chain, &relayer, COIN_AMOUNT, 10)?;

    Ok(BootstrapResult {
        chain,
        process,
        validator,
        relayer,
        user,
    })
}

// Wait for the wallet to reach the target amount when querying from the chain.
// This is to ensure that the chain has properly started and committed the genesis block
pub fn wait_wallet_amount(
    chain: &ChainCommand,
    user: &Wallet,
    target_amount: u64,
    remaining_retry: u16,
) -> Result<(), Error> {
    if remaining_retry == 0 {
        return Err(eyre!(
            "failed to wait for wallet to reach target amount. did the chain started properly?"
        ));
    }

    debug!(
        "waiting for wallet for {} to reach amount {}",
        user.id.0, target_amount
    );

    thread::sleep(Duration::from_secs(1));

    let query_res = chain.query_balance(&user.address, "samoleans");
    match query_res {
        Ok(amount) if amount == target_amount => Ok(()),
        _ => {
            trace!(
                "query balance return mismatch amount {:?}, retrying",
                query_res
            );
            wait_wallet_amount(chain, user, target_amount, remaining_retry - 1)
        }
    }
}
