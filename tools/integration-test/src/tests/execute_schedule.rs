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
            "Performing first IBC transfer from chain A to chain B with amount {}",
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
            "Performing second IBC transfer from chain B to chain A with amount {}",
            amount2
        );

        chains.node_b.chain_driver().ibc_transfer_token(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &chains.node_b.wallets().user1(),
            &chains.node_a.wallets().user1().address(),
            &chains.node_b.denom(),
            amount2,
        )?;

        let chain_a_link_opts = LinkParameters {
            src_port_id: channel.port_a.clone().into_value(),
            src_channel_id: channel.channel_id_a.clone().into_value(),
        };
        let chain_b_link_opts = LinkParameters {
            src_port_id: channel.port_b.clone().into_value(),
            src_channel_id: channel.channel_id_b.clone().into_value(),
        };

        let chain_a_link = Link::new_from_opts(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            chain_a_link_opts,
            true,
        )?;
        let chain_b_link = Link::new_from_opts(
            chains.handle_b().clone(),
            chains.handle_a().clone(),
            chain_b_link_opts,
            true,
        )?;

        let relay_path_a_to_b = chain_a_link.a_to_b;
        let relay_path_b_to_a = chain_b_link.a_to_b;

        relay_path_a_to_b.schedule_packet_clearing(None)?;
        relay_path_b_to_a.schedule_packet_clearing(None)?;

        assert_eq!(relay_path_a_to_b.dst_operational_data.len(), 1);
        assert_eq!(relay_path_b_to_a.dst_operational_data.len(), 1);

        chains.node_b.value().kill()?;

        match relay_path_a_to_b.execute_schedule() {
            Ok(_) => panic!("Expected an error"),
            Err(_e) => {
                assert_eq!(relay_path_a_to_b.dst_operational_data.len(), 0);
                assert_eq!(relay_path_b_to_a.dst_operational_data.len(), 1);
            }
        }

        Ok(())
    }
}
