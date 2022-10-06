use ibc_relayer::link::{Link, LinkParameters};
use ibc_test_framework::ibc::denom::derive_ibc_denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u64_range;

#[test]
fn test_ordered_channel_clear_no_conf_parallel() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelClearTest::new(false, false))
}

#[test]
fn test_ordered_channel_clear_no_conf_sequential() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelClearTest::new(false, true))
}

#[test]
fn test_ordered_channel_clear_conf_parallel() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelClearTest::new(true, false))
}

#[test]
fn test_ordered_channel_clear_conf_sequential() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelClearTest::new(true, true))
}

pub struct OrderedChannelClearTest {
    tx_confirmation: bool,
    sequential_batch_tx: bool,
}

impl OrderedChannelClearTest {
    pub fn new(tx_confirmation: bool, sequential_batch_tx: bool) -> Self {
        Self {
            tx_confirmation,
            sequential_batch_tx,
        }
    }
}

impl TestOverrides for OrderedChannelClearTest {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.tx_confirmation = self.tx_confirmation;
        config.chains[0].sequential_batch_tx = self.sequential_batch_tx;
        config.chains[1].sequential_batch_tx = self.sequential_batch_tx;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn channel_order(&self) -> Order {
        Order::Ordered
    }
}

impl BinaryChannelTest for OrderedChannelClearTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let amount = random_u64_range(1000, 5000);
        let num_msgs = 150_usize;
        let total_amount = amount * u64::try_from(num_msgs).unwrap();

        info!(
            "Performing {} IBC transfers with amount {} on an ordered channel",
            num_msgs, amount
        );

        chains.node_a.chain_driver().ibc_transfer_token_multiple(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a,
            amount,
            num_msgs,
        )?;

        sleep(Duration::from_secs(10));

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

        let chain_b_link_opts = LinkParameters {
            src_port_id: channel.port_b.clone().into_value(),
            src_channel_id: channel.channel_id_b.clone().into_value(),
        };

        let chain_b_link = Link::new_from_opts(
            chains.handle_b().clone(),
            chains.handle_a().clone(),
            chain_b_link_opts,
            true,
        )?;

        // Send the transfer (recv) packets from A to B over the channel.
        let mut relay_path_a_to_b = chain_a_link.a_to_b;
        relay_path_a_to_b.schedule_packet_clearing(None)?;
        relay_path_a_to_b.execute_schedule()?;

        sleep(Duration::from_secs(10));

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        // Wallet on chain B should have received IBC transfers with the ibc denomination.
        chains.node_b.chain_driver().assert_eventual_wallet_amount(
            &wallet_b.address(),
            total_amount,
            &denom_b.as_ref(),
        )?;

        // Send the packet acknowledgments from B to A.
        let mut relay_path_b_to_a = chain_b_link.a_to_b;
        relay_path_b_to_a.schedule_packet_clearing(None)?;
        relay_path_b_to_a.execute_schedule()?;

        sleep(Duration::from_secs(10));

        // Wallet on chain A should have sum of amounts deducted.
        chains.node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            balance_a - total_amount,
            &denom_a,
        )?;

        Ok(())
    }
}
