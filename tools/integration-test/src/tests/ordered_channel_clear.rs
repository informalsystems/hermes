use ibc_relayer::config::types::MaxMsgNum;
use ibc_relayer::link::{Link, LinkParameters};
use ibc_relayer::transfer::{build_and_send_transfer_messages, TransferOptions};
use ibc_relayer_types::events::IbcEvent;
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

#[test]
fn test_ordered_channel_clear_cli_equal() -> Result<(), Error> {
    run_binary_channel_test(&OrderedChannelClearEqualCLITest)
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
        let token = denom_a.with_amount(amount);

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
            &token.as_ref(),
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
            &denom_b.with_amount(total_amount).as_ref(),
        )?;

        // Send the packet acknowledgments from B to A.
        let mut relay_path_b_to_a = chain_b_link.a_to_b;
        relay_path_b_to_a.schedule_packet_clearing(None)?;
        relay_path_b_to_a.execute_schedule()?;

        sleep(Duration::from_secs(10));

        // Wallet on chain A should have sum of amounts deducted.
        let expected_a = denom_a.with_amount(balance_a.amount().checked_sub(total_amount).unwrap());

        chains
            .node_a
            .chain_driver()
            .assert_eventual_wallet_amount(&wallet_a.address(), &expected_a.as_ref())?;

        Ok(())
    }
}

pub struct OrderedChannelClearEqualCLITest;

impl TestOverrides for OrderedChannelClearEqualCLITest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.tx_confirmation = true;

        config.chains[0].sequential_batch_tx = true;
        config.chains[0].max_msg_num = MaxMsgNum::new(3).unwrap();

        config.chains[1].sequential_batch_tx = true;
        config.chains[1].max_msg_num = MaxMsgNum::new(3).unwrap();
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn channel_order(&self) -> Order {
        Order::Ordered
    }
}

// Tests the `packet_data_query_height` option for `hermes tx packet-recv` CLI option.
// Starts two chains A and B with `sequential_batch_tx` set to true and `max_msg_num` set to 3.
// Creates an ordered channels between A and B.
// Sends 5 ft transfers to chain A that will be included in 2 transactions:
//  - tx1: (1, 2, 3) sequences at some height `clear_height` on chain A
//  - tx2: (4, 5) sequences at `clear_height + 1` on chain A
// Sends to B all packets found on chain A in the block at `clear_height`, prepending an update_client message
// The test expects to get 4 IBC events from chain B, one for the update_client and 3 for the write_acknowledgment events
impl BinaryChannelTest for OrderedChannelClearEqualCLITest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let num_msgs = 5_usize;

        info!(
            "Performing {} IBC transfers on an ordered channel",
            num_msgs
        );

        let transfer_options = TransferOptions {
            src_port_id: channel.port_a.value().clone(),
            src_channel_id: channel.channel_id_a.value().clone(),
            amount: random_u64_range(1000, 5000).into(),
            denom: chains.node_a.denom().value().to_string(),
            receiver: Some(chains.node_b.wallets().user1().address().value().0.clone()),
            timeout_height_offset: 1000,
            timeout_duration: Duration::from_secs(0),
            number_msgs: num_msgs,
        };

        let events_with_heights = build_and_send_transfer_messages(
            chains.handle_a(),
            chains.handle_b(),
            &transfer_options,
        )?;

        let clear_height = events_with_heights.first().unwrap().height;
        let num_packets_at_clear_height = events_with_heights
            .iter()
            .filter(|&ev| ev.height == clear_height)
            .count();

        let expected_num_events = num_packets_at_clear_height + 1; // account for the update client

        let chain_a_link_opts = LinkParameters {
            src_port_id: channel.port_a.clone().into_value(),
            src_channel_id: channel.channel_id_a.into_value(),
        };

        let chain_a_link = Link::new_from_opts(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            chain_a_link_opts,
            true,
            true,
        )?;

        let events_returned: Vec<IbcEvent> = chain_a_link
            .relay_recv_packet_and_timeout_messages_with_packet_data_query_height(Some(
                clear_height,
            ))
            .unwrap();

        info!("recv packets sent, chain events: {:?}", events_returned);

        assert_eq!(expected_num_events, events_returned.len());

        Ok(())
    }
}
