use core::time::Duration;
use eyre::{eyre, Report as Error};
use std::thread;
use tracing::{debug, info, trace};

use crate::chain::builder::ChainBuilder;
use crate::chain::config;
use crate::chain::driver::ChainDriver;
use crate::chain::wallet::Wallet;
use crate::ibc::denom::Denom;
use crate::process::ChildProcess;
use crate::tagged::mono::Tagged as MonoTagged;
use crate::tagged::tag::Tag;
use crate::util;

use super::wallets::ChainWallets;

pub const STAKE_DENOM: &str = "stake";
pub const INITIAL_TOKEN_AMOUNT: u64 = 1_000_000_000_000;

pub struct ChainDeployment {
    pub chain_driver: ChainDriver,
    pub chain_process: ChildProcess,
    pub denom: Denom,
    pub wallets: ChainWallets,
}

impl<Chain> MonoTagged<Chain, ChainDeployment> {
    pub fn chain_driver<'a>(&'a self) -> MonoTagged<Chain, &'a ChainDriver> {
        self.map_ref(|c| &c.chain_driver)
    }

    pub fn wallets<'a>(&'a self) -> MonoTagged<Chain, &'a ChainWallets> {
        self.map_ref(|c| &c.wallets)
    }

    pub fn denom<'a>(&'a self) -> MonoTagged<Chain, &'a Denom> {
        self.map_ref(|c| &c.denom)
    }
}

pub fn bootstrap_single_chain(
    builder: &ChainBuilder,
) -> Result<MonoTagged<impl Tag, ChainDeployment>, Error> {
    let chain_driver = builder.new_chain();

    info!("created new chain: {}", chain_driver.chain_id);

    chain_driver.initialize()?;

    let validator = chain_driver.add_random_wallet("validator")?;
    let relayer = chain_driver.add_random_wallet("relayer")?;
    let user1 = chain_driver.add_random_wallet("user1")?;
    let user2 = chain_driver.add_random_wallet("user2")?;

    let stake_denom = Denom(STAKE_DENOM.to_string());
    let denom = Denom(format!("coin{:x}", util::random_u32()));

    chain_driver
        .add_genesis_account(&validator.address, &[(&stake_denom, INITIAL_TOKEN_AMOUNT)])?;

    chain_driver.add_genesis_validator(&validator.id, &stake_denom, INITIAL_TOKEN_AMOUNT)?;

    chain_driver.add_genesis_account(
        &user1.address,
        &[
            (&stake_denom, INITIAL_TOKEN_AMOUNT),
            (&denom, INITIAL_TOKEN_AMOUNT),
        ],
    )?;

    chain_driver.add_genesis_account(
        &user2.address,
        &[
            (&stake_denom, INITIAL_TOKEN_AMOUNT),
            (&denom, INITIAL_TOKEN_AMOUNT),
        ],
    )?;

    chain_driver.add_genesis_account(
        &relayer.address,
        &[
            (&stake_denom, INITIAL_TOKEN_AMOUNT),
            (&denom, INITIAL_TOKEN_AMOUNT),
        ],
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

    let deployment = <MonoTagged<(), _>>::new(ChainDeployment {
        chain_driver,
        chain_process,
        denom,
        wallets,
    });

    wait_wallet_amount(
        &deployment.chain_driver(),
        &deployment.wallets().relayer(),
        INITIAL_TOKEN_AMOUNT,
        &deployment.denom(),
        10,
    )?;

    Ok(deployment)
}

// Wait for the wallet to reach the target amount when querying from the chain.
// This is to ensure that the chain has properly started and committed the genesis block
pub fn wait_wallet_amount<Chain>(
    chain: &MonoTagged<Chain, &ChainDriver>,
    user: &MonoTagged<Chain, &Wallet>,
    target_amount: u64,
    denom: &MonoTagged<Chain, &Denom>,
    remaining_retry: u16,
) -> Result<(), Error> {
    if remaining_retry == 0 {
        return Err(eyre!(
            "failed to wait for wallet to reach target amount. did the chain started properly?"
        ));
    }

    debug!(
        "waiting for wallet for {} to reach amount {}",
        user.id().value().0,
        target_amount
    );

    thread::sleep(Duration::from_secs(2));

    let query_res = chain.query_balance(&user.address(), denom);

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
