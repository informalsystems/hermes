use ibc_relayer::channel::{extract_channel_id, Channel, ChannelSide};
use ibc_relayer_types::core::ics33_multihop::channel_path::ConnectionHops;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::assert_eventually_multihop_channel_established;
use ibc_test_framework::relayer::connection::create_connection_hop;
use ibc_test_framework::util::random::random_u128_range;

#[test]
fn test_multihop_transfer() -> Result<(), Error> {
    run_nary_connection_test(&MultihopTransferTest)
}

pub struct MultihopTransferTest;

impl TestOverrides for MultihopTransferTest {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.clients.misbehaviour = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

/// FIXME: Currently in order to have the correct channel at each step
/// the Channel is built manually.
/// Once the restore_from_event has been updated to be compatible with
/// multihop this test can be improved by using restore_from_event at each
/// step.
impl NaryConnectionTest<3> for MultihopTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 3>,
        connections: ConnectedConnections<Handle, 3>,
    ) -> Result<(), Error> {
        let chain_handle_a = chains.chain_handle_at::<0>()?;
        let chain_handle_b = chains.chain_handle_at::<1>()?;
        let chain_handle_c = chains.chain_handle_at::<2>()?;

        let node_a = chains.full_node_at::<0>()?;
        let node_c = chains.full_node_at::<2>()?;

        let client_b_on_a = chains.foreign_client_at::<1, 0>()?;
        let client_b_on_c = chains.foreign_client_at::<1, 2>()?;

        let connection_a_to_b = connections.connection_at::<0, 1>()?;
        let connection_b_to_a = connections.connection_at::<1, 0>()?;
        let connection_b_to_c = connections.connection_at::<1, 2>()?;
        let connection_c_to_b = connections.connection_at::<2, 1>()?;

        let connection_hop_a1 = create_connection_hop(
            chain_handle_a.value(),
            &chain_handle_a.value().id(),
            &chain_handle_b.value().id(),
            connection_a_to_b.connection_id_a.value(),
        )?;
        let connection_hop_a2 = create_connection_hop(
            chain_handle_b.value(),
            &chain_handle_b.value().id(),
            &chain_handle_c.value().id(),
            connection_b_to_c.connection_id_a.value(),
        )?;

        let connection_hop_c1 = create_connection_hop(
            chain_handle_c.value(),
            &chain_handle_c.value().id(),
            &chain_handle_b.value().id(),
            connection_c_to_b.connection_id_a.value(),
        )?;
        let connection_hop_c2 = create_connection_hop(
            chain_handle_b.value(),
            &chain_handle_b.value().id(),
            &chain_handle_a.value().id(),
            connection_b_to_a.connection_id_a.value(),
        )?;

        let connection_hops_a = ConnectionHops::new(vec![connection_hop_a1, connection_hop_a2]);
        let connection_hops_b = ConnectionHops::new(vec![connection_hop_c1, connection_hop_c2]);

        let channel_a_to_c = Channel {
            connection_delay: Default::default(),
            ordering: Ordering::Unordered,
            a_side: ChannelSide::new(
                chain_handle_a.value().clone(),
                client_b_on_a.id.clone(),
                connection_a_to_b.connection_id_a.value().clone(),
                Some(connection_hops_a.clone()),
                PortId::transfer(),
                None,
                None,
            ),
            b_side: ChannelSide::new(
                chain_handle_c.value().clone(),
                client_b_on_c.id.clone(),
                connection_c_to_b.connection_id_a.value().clone(),
                Some(connection_hops_b.clone()),
                PortId::transfer(),
                None,
                None,
            ),
        };

        let event = channel_a_to_c.build_chan_open_init_and_send()?;
        // FIXME: restore_from_event does not work with multihop
        //   * Will not fill multihop field
        //   * Uses counterparty connection for dst connection, but this results in an intermediary connection.
        //   * Potentially same issue with client
        let tmp_channel_c_to_a = Channel::restore_from_event(
            chain_handle_c.value().clone(),
            chain_handle_a.value().clone(),
            event,
        )?;

        let channel_id_a = tmp_channel_c_to_a.a_side.channel_id().cloned();

        // Extracting the channel from the event fails
        let channel_c_to_a = Channel {
            connection_delay: tmp_channel_c_to_a.connection_delay,
            ordering: tmp_channel_c_to_a.ordering,
            a_side: ChannelSide::new(
                tmp_channel_c_to_a.a_side.chain.clone(),
                client_b_on_c.id.clone(),
                connection_c_to_b.connection_id_a.value().clone(),
                Some(connection_hops_b.clone()),
                tmp_channel_c_to_a.a_side.port_id().clone(),
                channel_id_a.clone(),
                tmp_channel_c_to_a.a_side.version().cloned(),
            ),
            b_side: ChannelSide::new(
                tmp_channel_c_to_a.b_side.chain.clone(),
                client_b_on_a.id.clone(),
                connection_a_to_b.connection_id_a.value().clone(),
                Some(connection_hops_a.clone()),
                tmp_channel_c_to_a.b_side.port_id().clone(),
                tmp_channel_c_to_a.b_side.channel_id().cloned(),
                tmp_channel_c_to_a.b_side.version().cloned(),
            ),
        };

        std::thread::sleep(core::time::Duration::from_secs(10));
        let event = channel_c_to_a.build_chan_open_try_and_send()?;
        let channel_id_c = extract_channel_id(&event)?.clone();

        let channel_a_to_c = Channel {
            connection_delay: tmp_channel_c_to_a.connection_delay,
            ordering: tmp_channel_c_to_a.ordering,
            a_side: ChannelSide::new(
                chain_handle_a.value().clone(),
                client_b_on_a.id.clone(),
                connection_a_to_b.connection_id_a.value().clone(),
                Some(connection_hops_a.clone()),
                tmp_channel_c_to_a.b_side.port_id().clone(),
                Some(channel_id_c.clone()),
                tmp_channel_c_to_a.b_side.version().cloned(),
            ),
            b_side: ChannelSide::new(
                chain_handle_c.value().clone(),
                client_b_on_c.id.clone(),
                connection_c_to_b.connection_id_a.value().clone(),
                Some(connection_hops_b.clone()),
                tmp_channel_c_to_a.a_side.port_id().clone(),
                tmp_channel_c_to_a.a_side.channel_id().cloned(),
                tmp_channel_c_to_a.a_side.version().cloned(),
            ),
        };

        channel_a_to_c.build_chan_open_ack_and_send()?;
        std::thread::sleep(core::time::Duration::from_secs(10));

        // Extracting the channel from the event fails
        let channel_c_to_a = Channel {
            connection_delay: tmp_channel_c_to_a.connection_delay,
            ordering: tmp_channel_c_to_a.ordering,
            a_side: ChannelSide::new(
                tmp_channel_c_to_a.a_side.chain.clone(),
                client_b_on_c.id.clone(),
                connection_c_to_b.connection_id_a.value().clone(),
                Some(connection_hops_b.clone()),
                tmp_channel_c_to_a.a_side.port_id().clone(),
                channel_id_a.clone(),
                tmp_channel_c_to_a.a_side.version().cloned(),
            ),
            b_side: ChannelSide::new(
                tmp_channel_c_to_a.b_side.chain.clone(),
                client_b_on_a.id.clone(),
                connection_a_to_b.connection_id_a.value().clone(),
                Some(connection_hops_a.clone()),
                tmp_channel_c_to_a.b_side.port_id().clone(),
                Some(channel_id_c.clone()),
                tmp_channel_c_to_a.b_side.version().cloned(),
            ),
        };
        channel_c_to_a.build_chan_open_confirm_and_send()?;

        assert_eventually_multihop_channel_established(
            &chain_handle_a,
            &chain_handle_c,
            &channel_id_c,
            tmp_channel_c_to_a.b_side.port_id(),
            &connection_hops_a.connection_ids(),
            &connection_hops_b.connection_ids(),
        )?;

        let denom_a = node_a.denom();
        let wallet_a = node_a.wallets().user1().cloned();
        let wallet_c = node_c.wallets().user1().cloned();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_b_amount = random_u128_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chain_handle_a.id(),
            chain_handle_c.id(),
            a_to_b_amount,
            denom_a
        );

        let channel_id_a = TaggedChannelId::new(channel_a_to_c.a_channel_id().unwrap().clone());
        let port_a = DualTagged::new(channel_a_to_c.a_side.port_id().clone());
        let channel_id_c = TaggedChannelId::new(channel_a_to_c.b_channel_id().unwrap().clone());
        let port_c = DualTagged::new(channel_a_to_c.b_side.port_id().clone());

        relayer.with_supervisor(|| {
            node_a.chain_driver().ibc_transfer_token(
                &port_a.as_ref(),
                &channel_id_a.as_ref(),
                &wallet_a.as_ref(),
                &wallet_c.address(),
                &denom_a.with_amount(a_to_b_amount).as_ref(),
            )?;

            let denom_c = derive_ibc_denom(&port_c.as_ref(), &channel_id_c.as_ref(), &denom_a)?;

            info!(
                "Waiting for user on chain B to receive IBC transferred amount of {}",
                a_to_b_amount
            );

            node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &(balance_a - a_to_b_amount).as_ref(),
            )?;

            node_c.chain_driver().assert_eventual_wallet_amount(
                &wallet_c.address(),
                &denom_c.with_amount(a_to_b_amount).as_ref(),
            )?;

            Ok(())
        })
    }
}
