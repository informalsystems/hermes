use core::time::Duration;
use eyre::{eyre, Report as Error};
use std::thread;
use tracing::{debug, info, trace};

use crate::chain::builder::ChainBuilder;
use crate::chain::config;
use crate::chain::driver::ChainDriver;
use crate::chain::wallet::Wallet;
use crate::process::ChildProcess;
use crate::tagged::Tag;
use crate::util;

pub const STAKE_DENOM: &str = "stake";
pub const INITIAL_TOKEN_AMOUNT: u64 = 1_000_000_000_000;

pub struct ChainService<Chain> {
    pub chain: ChainDriver<Chain>,
    pub process: ChildProcess,
    pub validator: Wallet,
    pub relayer: Wallet,
    pub user1: Wallet,
    pub user2: Wallet,
    pub denom: String,
}

pub fn bootstrap_single_chain(builder: &ChainBuilder) -> Result<ChainService<impl Tag>, Error> {
    let chain = builder.new_chain();

    info!("created new chain: {}", chain.chain_id);

    chain.initialize()?;

    let validator = chain.add_random_wallet("validator")?;
    let relayer = chain.add_random_wallet("relayer")?;
    let user1 = chain.add_random_wallet("user1")?;
    let user2 = chain.add_random_wallet("user2")?;

    let denom = format!("coin{:x}", util::random_u32());

    chain.add_genesis_account(&validator.address, &[(STAKE_DENOM, INITIAL_TOKEN_AMOUNT)])?;

    chain.add_genesis_validator(&validator.id, STAKE_DENOM, INITIAL_TOKEN_AMOUNT)?;

    chain.add_genesis_account(
        &user1.address,
        &[
            (STAKE_DENOM, INITIAL_TOKEN_AMOUNT),
            (&denom, INITIAL_TOKEN_AMOUNT),
        ],
    )?;

    chain.add_genesis_account(
        &user2.address,
        &[
            (STAKE_DENOM, INITIAL_TOKEN_AMOUNT),
            (&denom, INITIAL_TOKEN_AMOUNT),
        ],
    )?;

    chain.add_genesis_account(
        &relayer.address,
        &[
            (STAKE_DENOM, INITIAL_TOKEN_AMOUNT),
            (&denom, INITIAL_TOKEN_AMOUNT),
        ],
    )?;

    chain.collect_gen_txs()?;

    let log_level = std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string());

    chain.update_chain_config(|config| {
        config::set_log_level(config, &log_level)?;
        config::set_rpc_port(config, chain.rpc_port)?;
        config::set_p2p_port(config, chain.p2p_port)?;
        config::set_timeout_commit(config, Duration::from_secs(1))?;
        config::set_timeout_propose(config, Duration::from_secs(1))?;

        Ok(())
    })?;

    let process = chain.start()?;

    wait_wallet_amount(&chain, &relayer, INITIAL_TOKEN_AMOUNT, &denom, 10)?;

    Ok(ChainService {
        chain,
        process,
        validator,
        relayer,
        user1,
        user2,
        denom,
    })
}

// Wait for the wallet to reach the target amount when querying from the chain.
// This is to ensure that the chain has properly started and committed the genesis block
pub fn wait_wallet_amount<Chain>(
    chain: &ChainDriver<Chain>,
    user: &Wallet,
    target_amount: u64,
    denom: &str,
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

    thread::sleep(Duration::from_secs(2));

    let query_res = chain.query_balance(&user.address, denom);
    match query_res {
        Ok(amount) => {
            if amount == target_amount {
                Ok(())
            } else {
                trace!(
                    "current balance amount {} does not match the target amount {}",
                    amount,
                    target_amount
                );

                wait_wallet_amount(chain, user, target_amount, denom, remaining_retry - 1)
            }
        }
        _ => {
            trace!(
                "query balance return mismatch amount {:?}, retrying",
                query_res
            );
            wait_wallet_amount(chain, user, target_amount, denom, remaining_retry - 1)
        }
    }
}
