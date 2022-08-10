use std::time::Instant;

use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::config::types::max_msg_num::MaxMsgNum;
use ibc_test_framework::chain::config;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::transfer::build_transfer_message;

#[test]
fn test_sequential_commit() -> Result<(), Error> {
    run_binary_channel_test(&SequentialCommitTest)
}

pub struct SequentialCommitTest;

impl TestOverrides for SequentialCommitTest {
    fn modify_node_config(&self, config: &mut toml::Value) -> Result<(), Error> {
        config::set_timeout_commit(config, Duration::from_millis(500))?;
        config::set_timeout_propose(config, Duration::from_millis(500))?;
        config::set_mempool_version(config, "v1")?;

        Ok(())
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        let chain_config_a = &mut config.chains[0];
        chain_config_a.max_msg_num = MaxMsgNum::new(3).unwrap();
        chain_config_a.sequential_batch_tx = true;

        let chain_config_b = &mut config.chains[1];
        chain_config_b.max_msg_num = MaxMsgNum::new(3).unwrap();
        chain_config_b.sequential_batch_tx = false;
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

            let transfer_message = build_transfer_message(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &wallet_a.as_ref(),
                &wallet_b.address(),
                &denom_a,
                100,
            )?;

            let messages = TrackedMsgs::new_static(vec![transfer_message; 15], "test_error_events");

            let start = Instant::now();

            chains.handle_a().send_messages_and_wait_commit(messages)?;

            let end = Instant::now();

            let duration = end.duration_since(start);

            info!("time taken to send 15 messages on chain A: {:?}", duration);
        }

        {
            let denom_b = chains.node_b.denom();

            let transfer_message = build_transfer_message(
                &channel.port_b.as_ref(),
                &channel.channel_id_b.as_ref(),
                &wallet_b.as_ref(),
                &wallet_a.address(),
                &denom_b,
                100,
            )?;

            let messages = TrackedMsgs::new_static(vec![transfer_message; 15], "test_error_events");

            let start = Instant::now();

            chains.handle_b().send_messages_and_wait_commit(messages)?;

            let end = Instant::now();

            let duration = end.duration_since(start);

            info!("time taken to send 15 messages on chain B: {:?}", duration);
        }

        Ok(())
    }
}
