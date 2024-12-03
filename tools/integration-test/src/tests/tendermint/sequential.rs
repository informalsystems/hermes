use std::time::Instant;

use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::config::types::max_msg_num::MaxMsgNum;
use ibc_relayer::config::ChainConfig;
use ibc_test_framework::chain::chain_type::ChainType;
use ibc_test_framework::chain::config;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::transfer::build_transfer_message;

const MESSAGES_PER_BATCH: usize = 5;
const TOTAL_TRANSACTIONS: usize = 5;
const TOTAL_MESSAGES: usize = MESSAGES_PER_BATCH * TOTAL_TRANSACTIONS;
const BLOCK_TIME_MILLIS: u64 = 1000;
const BLOCK_TIME: Duration = Duration::from_millis(BLOCK_TIME_MILLIS);

#[test]
fn test_sequential_commit() -> Result<(), Error> {
    run_binary_channel_test(&SequentialCommitTest)
}

pub struct SequentialCommitTest;

impl TestOverrides for SequentialCommitTest {
    fn modify_node_config(&self, config: &mut toml::Value) -> Result<(), Error> {
        let config = if let Some(config) = config.get_mut("ledger") {
            // Namada
            config
                .get_mut("cometbft")
                .ok_or_else(|| eyre!("expect cometbft section"))?
        } else {
            config
        };

        config::cosmos::set_timeout_commit(config, BLOCK_TIME)?;
        config::cosmos::set_timeout_propose(config, BLOCK_TIME)?;

        // Enable priority mempool
        config::cosmos::set_mempool_version(config, "v1")?;

        Ok(())
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        // Use sequential batching for chain A, and default parallel batching for chain B
        match &mut config.chains[0] {
            ChainConfig::CosmosSdk(chain_config_a) | ChainConfig::Namada(chain_config_a) => {
                chain_config_a.max_msg_num = MaxMsgNum::new(MESSAGES_PER_BATCH).unwrap();
                chain_config_a.sequential_batch_tx = true;
            }
        };

        match &mut config.chains[1] {
            ChainConfig::CosmosSdk(chain_config_b) | ChainConfig::Namada(chain_config_b) => {
                chain_config_b.max_msg_num = MaxMsgNum::new(MESSAGES_PER_BATCH).unwrap();
                chain_config_b.sequential_batch_tx = false;
            }
        };
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for SequentialCommitTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let wallet_a = chains.node_a.wallets().relayer().cloned();
        let wallet_b = chains.node_b.wallets().relayer().cloned();

        {
            let denom_a = chains.node_a.denom();

            let mut transfer_messages = Vec::new();
            for i in 0..TOTAL_MESSAGES {
                let transfer_message = build_transfer_message(
                    &channel.port_a.as_ref(),
                    &channel.channel_id_a.as_ref(),
                    &wallet_a.as_ref(),
                    &wallet_b.address(),
                    &denom_a.with_amount(100u64).as_ref(),
                    Duration::from_secs(30),
                    // Namada batch transaction can't have the exact same message
                    Some(i.to_string()),
                )?;
                transfer_messages.push(transfer_message);
            }

            let messages = TrackedMsgs::new_static(transfer_messages, "test_sequential_commit");

            let start = Instant::now();

            chains.handle_a().send_messages_and_wait_commit(messages)?;

            let end = Instant::now();

            let duration = end.duration_since(start);

            info!(
                "time taken to send {} messages on chain A: {:?}",
                TOTAL_MESSAGES, duration
            );

            let (min_duration, max_duration) = match chains.node_a.chain_driver().value().chain_type
            {
                ChainType::Namada => (
                    Duration::from_millis((BLOCK_TIME_MILLIS * TOTAL_TRANSACTIONS as u64) - 1000),
                    Duration::from_millis(
                        (BLOCK_TIME_MILLIS * TOTAL_TRANSACTIONS as u64 * 2) + 1000,
                    ),
                ),
                _ => {
                    // Time taken for submitting sequential batches should be around number of transactions * block time
                    (
                        Duration::from_millis(
                            (BLOCK_TIME_MILLIS * TOTAL_TRANSACTIONS as u64) - 1000,
                        ),
                        Duration::from_millis(
                            (BLOCK_TIME_MILLIS * TOTAL_TRANSACTIONS as u64) + 1000,
                        ),
                    )
                }
            };
            assert!(duration > min_duration);
            assert!(duration < max_duration);
        }

        {
            let denom_b = chains.node_b.denom();

            let mut transfer_messages = Vec::new();
            for i in 0..TOTAL_MESSAGES {
                let transfer_message = build_transfer_message(
                    &channel.port_b.as_ref(),
                    &channel.channel_id_b.as_ref(),
                    &wallet_b.as_ref(),
                    &wallet_a.address(),
                    &denom_b.with_amount(100u64).as_ref(),
                    Duration::from_secs(30),
                    // Namada batch transaction can't have the exact same message
                    Some(i.to_string()),
                )?;
                transfer_messages.push(transfer_message);
            }

            let messages = TrackedMsgs::new_static(transfer_messages, "test_sequential_commit");

            let start = Instant::now();

            chains.handle_b().send_messages_and_wait_commit(messages)?;

            let end = Instant::now();

            let duration = end.duration_since(start);

            // Time taken for submitting sequential batches should be around a single block time,
            // since the number of transactions are small enough to fit in a single block.

            info!(
                "time taken to send {} messages on chain B: {:?}",
                TOTAL_MESSAGES, duration
            );

            let max_duration = match chains.node_b.chain_driver().value().chain_type {
                ChainType::Namada => {
                    // Shorter than the sequential batches
                    Duration::from_millis(BLOCK_TIME_MILLIS * TOTAL_TRANSACTIONS as u64 * 2)
                }
                _ => Duration::from_millis(BLOCK_TIME_MILLIS * 2),
            };
            assert!(duration < max_duration);
        }

        Ok(())
    }
}
