use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

use ibc_relayer::link::{Link, LinkParameters};

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
        let amount2 = random_u64_range(1000, 5000);

        info!(
            "Performing first IBC transfer with amount {}, which should be relayed because its an ordered channel",
            amount1
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &chains.node_a.wallets().user1(),
            &chains.node_b.wallets().user1().address(),
            &chains.node_a.denom(),
            amount1,
        )?;

        info!(
            "Performing second IBC transfer with amount {}, which should be relayed because its an ordered channel",
            amount2
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &chains.node_a.wallets().user1(),
            &chains.node_b.wallets().user1().address(),
            &chains.node_a.denom(),
            amount2,
        )?;

        let link_opts = LinkParameters {
            src_port_id: channel.port_a.clone().into_value(),
            src_channel_id: channel.channel_id_a.clone().into_value(),
        };
        let link = Link::new_from_opts(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            link_opts,
            true,
        )?;
        let relay_path = link.a_to_b;

        relay_path.schedule_packet_clearing(None)?;

        // assert_eq!(relay_path.dst_operational_data.len(), 2);
        assert_eq!(relay_path.dst_operational_data.len(), 1);

        chains.node_b.value().kill()?;

        match relay_path.execute_schedule() {
            Ok(_) => panic!("Expected an error"),
            Err(_e) => {
                // assert_eq!(relay_path.dst_operational_data.len(), 1);
                assert_eq!(relay_path.dst_operational_data.len(), 0);
            }
        }

        Ok(())
    }
}
