use ibc::core::ics04_channel::Version;
use ibc::events::IbcEvent;
use ibc_test_framework::prelude::*;
use ibc_test_framework::util::random::random_u128_range;
use std::thread;

#[test]
fn test_no_forward_relayer() -> Result<(), Error> {
    run_binary_channel_test(&NoForwardRelayerTest)
}

#[test]
fn test_forward_relayer() -> Result<(), Error> {
    run_binary_channel_test(&ForwardRelayerTest)
}

#[test]
fn test_auto_forward_relayer() -> Result<(), Error> {
    run_binary_channel_test(&AutoForwardRelayerTest)
}

#[test]
fn test_timeout_fee() -> Result<(), Error> {
    run_binary_channel_test(&TimeoutFeeTest)
}

#[test]
fn test_pay_packet_fee_async() -> Result<(), Error> {
    run_binary_channel_test(&PayPacketFeeAsyncTest)
}

#[test]
fn test_non_fee_channel() -> Result<(), Error> {
    run_binary_channel_test(&NonFeeChannelTest)
}

struct ForwardRelayerTest;
struct AutoForwardRelayerTest;
struct NoForwardRelayerTest;
struct TimeoutFeeTest;
struct PayPacketFeeAsyncTest;
struct NonFeeChannelTest;

impl TestOverrides for ForwardRelayerTest {
    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl TestOverrides for AutoForwardRelayerTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.auto_register_counterparty_address = true;
    }

    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl TestOverrides for NoForwardRelayerTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.auto_register_counterparty_address = false;
    }

    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl TestOverrides for TimeoutFeeTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl TestOverrides for PayPacketFeeAsyncTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl TestOverrides for NonFeeChannelTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.auto_register_counterparty_address = true;
    }
}

impl BinaryChannelTest for NoForwardRelayerTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let denom_a = chains.node_a.denom();

        let port_a = channel.port_a.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let relayer_a = wallets_a.relayer();

        let user_a = wallets_a.user1();
        let user_b = wallets_b.user1();

        let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

        let relayer_balance_a = chain_driver_a.query_balance(&relayer_a.address(), &denom_a)?;

        let send_amount = random_u128_range(1000, 2000);
        let receive_fee = random_u128_range(300, 400);
        let ack_fee = random_u128_range(200, 300);
        let timeout_fee = random_u128_range(100, 200);

        let total_sent = send_amount + receive_fee + ack_fee + timeout_fee;

        let balance_a2 = balance_a1 - total_sent;

        chain_driver_a.ibc_token_transfer_with_fee(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
            &denom_a.with_amount(receive_fee).as_ref(),
            &denom_a.with_amount(ack_fee).as_ref(),
            &denom_a.with_amount(timeout_fee).as_ref(),
            Duration::from_secs(60),
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!("Expect user A's balance after transfer: {}", balance_a2);

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a2.as_ref())?;

        chain_driver_b.assert_eventual_wallet_amount(
            &user_b.address(),
            &denom_b.with_amount(send_amount).as_ref(),
        )?;

        info!(
            "Expect user to be refunded receive fee {} and timeout fee {} and go from {} to {}",
            receive_fee,
            timeout_fee,
            balance_a2,
            balance_a2.amount() + receive_fee + timeout_fee
        );

        // receive fee and timeout fee should be refunded,
        // as there is no counterparty address registered.
        chain_driver_a.assert_eventual_wallet_amount(
            &user_a.address(),
            &(balance_a2 + receive_fee + timeout_fee).as_ref(),
        )?;

        info!(
            "Expect relayer to receive ack fee {} and go from {} to {}",
            ack_fee,
            relayer_balance_a,
            relayer_balance_a.amount() + ack_fee,
        );

        chain_driver_a.assert_eventual_wallet_amount(
            &relayer_a.address(),
            &(relayer_balance_a + ack_fee).as_ref(),
        )?;

        Ok(())
    }
}

impl BinaryChannelTest for ForwardRelayerTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let chain_id_a = chain_driver_a.chain_id();
        let chain_id_b = chain_driver_b.chain_id();

        let denom_a = chains.node_a.denom();

        let port_a = channel.port_a.as_ref();
        let port_b = channel.port_b.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();

        let channel_id_b = channel.channel_id_b.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let relayer_a = wallets_a.relayer();
        let relayer_b = wallets_b.relayer();

        info!(
            "registering counterparty address of relayer {} on chain {} to be {} on chain {}",
            relayer_b.address(),
            chain_id_b,
            relayer_a.address(),
            chain_id_a
        );

        {
            let counterparty_address =
                chain_driver_b.query_counterparty_address(&channel_id_b, &relayer_b.address())?;

            assert_eq(
                "counterparty address should be None before registering",
                &counterparty_address,
                &None,
            )?;
        }

        chain_driver_b.register_counterparty_address(
            &relayer_b,
            &relayer_a.address(),
            &channel_id_b,
            &port_b,
        )?;

        {
            let counterparty_address =
                chain_driver_b.query_counterparty_address(&channel_id_b, &relayer_b.address())?;

            assert_eq(
                "counterparty address should match registered address",
                &counterparty_address,
                &Some(relayer_a.address().cloned()),
            )?;
        }

        let user_a = wallets_a.user1();
        let user_b = wallets_b.user1();

        let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

        let relayer_balance_a = chain_driver_a.query_balance(&relayer_a.address(), &denom_a)?;

        let send_amount = random_u128_range(1000, 2000);
        let receive_fee = random_u128_range(300, 400);
        let ack_fee = random_u128_range(200, 300);
        let timeout_fee = random_u128_range(100, 200);

        let total_sent = send_amount + receive_fee + ack_fee + timeout_fee;

        let balance_a2 = balance_a1 - total_sent;

        chain_driver_a.ibc_token_transfer_with_fee(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
            &denom_a.with_amount(receive_fee).as_ref(),
            &denom_a.with_amount(ack_fee).as_ref(),
            &denom_a.with_amount(timeout_fee).as_ref(),
            Duration::from_secs(60),
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!("Expect user A's balance after transfer: {}", balance_a2);

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a2.as_ref())?;

        chain_driver_b.assert_eventual_wallet_amount(
            &user_b.address(),
            &denom_b.with_amount(send_amount).as_ref(),
        )?;

        info!(
            "Expect user to be refunded receive timeout fee {} and go from {} to {}",
            timeout_fee,
            balance_a2,
            balance_a2.amount() + timeout_fee
        );

        chain_driver_a.assert_eventual_wallet_amount(
            &user_a.address(),
            &(balance_a2 + timeout_fee).as_ref(),
        )?;

        info!(
            "Expect relayer to receive ack fee {} and receive fee {} and go from {} to {}",
            ack_fee,
            receive_fee,
            relayer_balance_a,
            relayer_balance_a.amount() + ack_fee + receive_fee,
        );

        chain_driver_a.assert_eventual_wallet_amount(
            &relayer_a.address(),
            &(relayer_balance_a + ack_fee + receive_fee).as_ref(),
        )?;

        Ok(())
    }
}

impl BinaryChannelTest for AutoForwardRelayerTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let denom_a = chains.node_a.denom();

        let port_a = channel.port_a.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let relayer_a = wallets_a.relayer();

        let user_a = wallets_a.user1();
        let user_b = wallets_b.user1();

        let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

        let relayer_balance_a = chain_driver_a.query_balance(&relayer_a.address(), &denom_a)?;

        let send_amount = random_u128_range(1000, 2000);
        let receive_fee = random_u128_range(300, 400);
        let ack_fee = random_u128_range(200, 300);
        let timeout_fee = random_u128_range(100, 200);

        let total_sent = send_amount + receive_fee + ack_fee + timeout_fee;

        let balance_a2 = balance_a1 - total_sent;

        chain_driver_a.ibc_token_transfer_with_fee(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
            &denom_a.with_amount(receive_fee).as_ref(),
            &denom_a.with_amount(ack_fee).as_ref(),
            &denom_a.with_amount(timeout_fee).as_ref(),
            Duration::from_secs(60),
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        info!("Expect user A's balance after transfer: {}", balance_a2);

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a2.as_ref())?;

        chain_driver_b.assert_eventual_wallet_amount(
            &user_b.address(),
            &denom_b.with_amount(send_amount).as_ref(),
        )?;

        info!(
            "Expect user to be refunded receive timeout fee {} and go from {} to {}",
            timeout_fee,
            balance_a2,
            balance_a2.amount() + timeout_fee
        );

        chain_driver_a.assert_eventual_wallet_amount(
            &user_a.address(),
            &(balance_a2 + timeout_fee).as_ref(),
        )?;

        info!(
            "Expect relayer to receive ack fee {} and receive fee {} and go from {} to {}",
            ack_fee,
            receive_fee,
            relayer_balance_a,
            relayer_balance_a.amount() + ack_fee + receive_fee,
        );

        chain_driver_a.assert_eventual_wallet_amount(
            &relayer_a.address(),
            &(relayer_balance_a + ack_fee + receive_fee).as_ref(),
        )?;

        Ok(())
    }
}

impl BinaryChannelTest for TimeoutFeeTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();

        let denom_a = chains.node_a.denom();

        let port_a = channel.port_a.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let relayer_a = wallets_a.relayer();

        let user_a = wallets_a.user1();
        let user_b = wallets_b.user1();

        let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

        let relayer_balance_a = chain_driver_a.query_balance(&relayer_a.address(), &denom_a)?;

        let send_amount = random_u128_range(1000, 2000);
        let receive_fee = random_u128_range(300, 400);
        let ack_fee = random_u128_range(200, 300);
        let timeout_fee = random_u128_range(100, 200);

        let total_sent = send_amount + receive_fee + ack_fee + timeout_fee;

        let balance_a2 = balance_a1 - total_sent;

        chain_driver_a.ibc_token_transfer_with_fee(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
            &denom_a.with_amount(receive_fee).as_ref(),
            &denom_a.with_amount(ack_fee).as_ref(),
            &denom_a.with_amount(timeout_fee).as_ref(),
            Duration::from_secs(5),
        )?;

        info!("Expect user A's balance after transfer: {}", balance_a2);

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a2.as_ref())?;

        // Sleep to wait for IBC packet to timeout before start relaying
        thread::sleep(Duration::from_secs(6));

        relayer.with_supervisor(|| {
            info!(
                "Expect user to be refunded send amount {}, receive fee {} and ack fee {} and go from {} to {}",
                send_amount,
                receive_fee,
                ack_fee,
                balance_a2,
                balance_a2.amount() + send_amount + receive_fee + ack_fee
            );

            chain_driver_a.assert_eventual_wallet_amount(
                &user_a.address(),
                &(balance_a2 + send_amount + receive_fee + ack_fee).as_ref(),
            )?;

            info!(
                "Expect relayer to receive timeout fee {} and go from {} to {}",
                timeout_fee,
                relayer_balance_a,
                relayer_balance_a.amount() + timeout_fee,
            );

            chain_driver_a.assert_eventual_wallet_amount(
                &relayer_a.address(),
                &(relayer_balance_a + timeout_fee).as_ref(),
            )?;

            Ok(())
        })
    }
}

impl BinaryChannelTest for PayPacketFeeAsyncTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let chain_id_a = chain_driver_a.chain_id();
        let chain_id_b = chain_driver_b.chain_id();

        let denom_a = chains.node_a.denom();

        let port_a = channel.port_a.as_ref();
        let port_b = channel.port_b.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();

        let channel_id_b = channel.channel_id_b.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let relayer_a = wallets_a.relayer();
        let relayer_b = wallets_b.relayer();

        info!(
            "registering counterparty address of relayer {} on chain {} to be {} on chain {}",
            relayer_b.address(),
            chain_id_b,
            relayer_a.address(),
            chain_id_a
        );

        chain_driver_b.register_counterparty_address(
            &relayer_b,
            &relayer_a.address(),
            &channel_id_b,
            &port_b,
        )?;

        let user_a = wallets_a.user1();

        let user_b = wallets_b.user1();

        let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

        let relayer_balance_a = chain_driver_a.query_balance(&relayer_a.address(), &denom_a)?;

        let send_amount = random_u128_range(1000, 2000);
        let receive_fee = random_u128_range(300, 400);
        let ack_fee = random_u128_range(200, 300);
        let timeout_fee = random_u128_range(100, 200);

        let events = chain_driver_a.ibc_token_transfer_with_fee(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
            &denom_a.with_amount(receive_fee).as_ref(),
            &denom_a.with_amount(ack_fee).as_ref(),
            &denom_a.with_amount(timeout_fee).as_ref(),
            Duration::from_secs(60),
        )?;

        let total_sent = send_amount + receive_fee + ack_fee + timeout_fee;
        let balance_a2 = balance_a1 - total_sent;
        info!("Expect user A's balance after transfer: {}", balance_a2);

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a2.as_ref())?;

        let send_packet_event = events
            .into_iter()
            .find_map(|event| match event {
                IbcEvent::SendPacket(e) => Some(e),
                _ => None,
            })
            .ok_or_else(|| eyre!("expect send packet event"))?;

        let sequence = send_packet_event.packet.sequence;

        {
            let packets = chain_driver_a.query_incentivized_packets(&channel_id_a, &port_a)?;

            info!("incenvitized packets: {:?}", packets);

            assert_eq!(packets.len(), 1);

            let packet = &packets[0];
            assert_eq!(packet.packet_id.sequence, sequence);

            assert_eq!(packet.packet_fees.len(), 1);
            let packet_fee = &packet.packet_fees[0];

            assert_eq!(packet_fee.fee.recv_fee.len(), 1);
            assert_eq!(packet_fee.fee.ack_fee.len(), 1);
            assert_eq!(packet_fee.fee.timeout_fee.len(), 1);

            assert_eq!(
                &packet_fee.fee.recv_fee[0],
                &denom_a.with_amount(receive_fee).value().as_coin(),
            );
            assert_eq!(
                &packet_fee.fee.ack_fee[0],
                &denom_a.with_amount(ack_fee).value().as_coin()
            );

            assert_eq!(
                &packet_fee.fee.timeout_fee[0],
                &denom_a.with_amount(timeout_fee).value().as_coin(),
            );

            assert_eq!(
                packet_fee.refund_address.as_ref(),
                user_a.value().address.as_str(),
            );
        }

        let receive_fee_2 = random_u128_range(300, 400);
        let ack_fee_2 = random_u128_range(200, 300);
        let timeout_fee_2 = random_u128_range(100, 200);

        chain_driver_a.pay_packet_fee(
            &port_a,
            &channel_id_a,
            &DualTagged::new(sequence),
            &user_a,
            &denom_a.with_amount(receive_fee_2).as_ref(),
            &denom_a.with_amount(ack_fee_2).as_ref(),
            &denom_a.with_amount(timeout_fee_2).as_ref(),
        )?;

        let total_sent_2 = receive_fee_2 + ack_fee_2 + timeout_fee_2;
        let balance_a3 = balance_a2 - total_sent_2;

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a3.as_ref())?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        relayer.with_supervisor(|| {
            chain_driver_b.assert_eventual_wallet_amount(
                &user_b.address(),
                &denom_b.with_amount(send_amount).as_ref(),
            )?;

            chain_driver_a.assert_eventual_wallet_amount(
                &user_a.address(),
                &(balance_a3 + timeout_fee + timeout_fee_2).as_ref(),
            )?;

            chain_driver_a.assert_eventual_wallet_amount(
                &relayer_a.address(),
                &(relayer_balance_a + ack_fee + receive_fee + ack_fee_2 + receive_fee_2).as_ref(),
            )?;

            Ok(())
        })
    }
}

impl BinaryChannelTest for NonFeeChannelTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let denom_a = chains.node_a.denom();

        let port_a = channel.port_a.as_ref();
        let port_b = channel.port_b.as_ref();
        let channel_id_a = channel.channel_id_a.as_ref();
        let channel_id_b = channel.channel_id_b.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let user_a = wallets_a.user1();
        let user_b = wallets_b.user1();

        let relayer_a = wallets_a.relayer();
        let relayer_b = wallets_b.relayer();

        let balance_a1 = chain_driver_a.query_balance(&user_a.address(), &denom_a)?;

        let send_amount = random_u128_range(1000, 2000);

        {
            let res = chain_driver_b.register_counterparty_address(
                &relayer_b,
                &relayer_a.address(),
                &channel_id_b,
                &port_b,
            );

            assert!(res.is_err());
        }

        {
            let res = chain_driver_a.ibc_token_transfer_with_fee(
                &port_a,
                &channel_id_a,
                &user_a,
                &user_b.address(),
                &denom_a.with_amount(send_amount).as_ref(),
                &denom_a.with_amount(10).as_ref(),
                &denom_a.with_amount(10).as_ref(),
                &denom_a.with_amount(10).as_ref(),
                Duration::from_secs(60),
            );

            assert!(res.is_err());
        }

        let balance_a2 = balance_a1 - send_amount;

        chain_driver_a.ibc_transfer_token(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
        )?;

        let denom_b = derive_ibc_denom(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        chain_driver_a.assert_eventual_wallet_amount(&user_a.address(), &balance_a2.as_ref())?;

        chain_driver_b.assert_eventual_wallet_amount(
            &user_b.address(),
            &denom_b.with_amount(send_amount).as_ref(),
        )?;

        Ok(())
    }
}
