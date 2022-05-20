//! This test ensures that the `RelayPath::execute_schedule` method does not
//! drop any pending scheduled operational data when a prior transaction fails
//! to send. Subsequent pieces of operational data that were scheduled should
//! be re-queued and not dropped.
//!
//! In order to test this behavior, the test manually relays at least 2 IBC transfers
//! from chain A to chain B. Chain B is then shut down in order to force the transactions
//! to be queued up again for re-submission. It is expected that the first transfer
//! be dropped and not be present in the pending queue, but all of the subsequent
//! transactions should exist in the pending queue.

use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

use ibc_relayer::link::{Link, LinkParameters};

const NUM_TXS: usize = 10;

#[test]
fn test_execute_schedule() -> Result<(), Error> {
    run_binary_channel_test(&ExecuteScheduleTest)
}

pub struct ExecuteScheduleTest;

impl TestOverrides for ExecuteScheduleTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ExecuteScheduleTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let amount1 = random_u64_range(1000, 5000);

        let chain_a_link_opts = LinkParameters {
            src_port_id: channel.port_a.clone().into_value(),
            src_channel_id: channel.channel_id_a.clone().into_value(),
        };

        let chain_a_link = Link::new_from_opts(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            chain_a_link_opts,
            true,
        )?;

        let mut relay_path_a_to_b = chain_a_link.a_to_b;

        for i in 0..NUM_TXS {
            chains.node_a.chain_driver().ibc_transfer_token(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &chains.node_a.wallets().user1(),
                &chains.node_b.wallets().user1().address(),
                &chains.node_a.denom(),
                amount1,
            )?;

            relay_path_a_to_b.schedule_packet_clearing(None)?;

            info!("Performing IBC transfer #{} from chain A to chain B", i);
        }

        assert_eq!(relay_path_a_to_b.dst_operational_data.len(), NUM_TXS);

        chains.node_b.value().kill()?;

        match relay_path_a_to_b.execute_schedule() {
            Ok(_) => panic!("Expected an error when relaying tx from A to B"),
            Err(_) => assert_eq!(relay_path_a_to_b.dst_operational_data.len(), NUM_TXS - 1),
        }

        Ok(())
    }
}
