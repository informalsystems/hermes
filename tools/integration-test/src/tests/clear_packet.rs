use std::thread;

use ibc_relayer::chain::counterparty::pending_packet_summary;
use ibc_relayer::config::ChainConfig;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::query_identified_channel_end;
use ibc_test_framework::util::random::random_u128_range;

#[test]
fn test_clear_packet() -> Result<(), Error> {
    run_binary_channel_test(&ClearPacketTest)
}

#[test]
fn test_clear_packet_recovery() -> Result<(), Error> {
    run_binary_channel_test(&ClearPacketRecoveryTest)
}

#[test]
fn test_clear_packet_no_scan() -> Result<(), Error> {
    run_binary_channel_test(&ClearPacketNoScanTest)
}

#[test]
fn test_clear_packet_override() -> Result<(), Error> {
    run_binary_channel_test(&ClearPacketOverrideTest)
}

#[test]
fn test_clear_packet_sequences() -> Result<(), Error> {
    run_binary_channel_test(&ClearPacketSequencesTest)
}

pub struct ClearPacketTest;
pub struct ClearPacketRecoveryTest;
pub struct ClearPacketNoScanTest;
pub struct ClearPacketOverrideTest;
pub struct ClearPacketSequencesTest;

impl TestOverrides for ClearPacketTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        // Disabling client workers and clear_on_start should make the relayer not
        // relay any packet it missed before starting.
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
        config.mode.channels.enabled = false;

        config.mode.packets.enabled = true;
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 0;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    // Unordered channel: will permit gaps in the sequence of relayed packets
    fn channel_order(&self) -> Ordering {
        Ordering::Unordered
    }
}

impl TestOverrides for ClearPacketRecoveryTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.packets.enabled = true;
        config.mode.packets.clear_on_start = true;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ClearPacketTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
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

        let amount1 = denom_a.with_amount(random_u128_range(1000, 5000));

        info!(
            "Performing IBC transfer with amount {}, which should *not* be relayed",
            amount1
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &amount1.as_ref(),
        )?;

        sleep(Duration::from_secs(1));

        // Spawn the supervisor only after the first IBC transfer
        relayer.with_supervisor(|| {
            sleep(Duration::from_secs(1));

            let amount2 = denom_a.with_amount(random_u128_range(1000, 5000));

            info!(
                "Performing IBC transfer with amount {}, which should be relayed",
                amount2
            );

            chains.node_a.chain_driver().ibc_transfer_token(
                &channel.port_a.as_ref(),
                &channel.channel_id_a.as_ref(),
                &wallet_a.as_ref(),
                &wallet_b.address(),
                &amount2.as_ref(),
            )?;

            sleep(Duration::from_secs(1));

            let amount_b = amount2.transfer(
                &chains.node_b.chain_driver().value().chain_type,
                &channel.port_b.as_ref(),
                &channel.channel_id_b.as_ref(),
            )?;

            // Wallet on chain A should have both amount deducted.
            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &(balance_a - amount1.amount() - amount2.amount()).as_ref(),
            )?;

            // Wallet on chain B should only receive the second IBC transfer
            chains
                .node_b
                .chain_driver()
                .assert_eventual_wallet_amount(&wallet_b.address(), &amount_b.as_ref())?;

            Ok(())
        })
    }
}

impl BinaryChannelTest for ClearPacketRecoveryTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();
        let denom_b1 = chains.node_b.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let relayer_wallet_b = chains.node_b.wallets().relayer().cloned();

        // mess up the cached account sequence in ChainHandle of chain B
        chains.node_b.chain_driver().local_transfer_token(
            &relayer_wallet_b.as_ref(),
            &wallet_b.address(),
            &denom_b1.with_amount(100u64).as_ref(),
        )?;

        let amount1 = random_u128_range(1000, 5000);

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(amount1).as_ref(),
        )?;

        let denom_b2 = derive_ibc_denom(
            &chains.node_b.chain_driver().value().chain_type,
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        relayer.with_supervisor(|| {
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(amount1).as_ref(),
            )?;

            Ok(())
        })
    }
}

impl TestOverrides for ClearPacketNoScanTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        // Disabling the client workers and clear_on_start should make the relayer not
        // relay any packet it missed before starting.
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
        config.mode.channels.enabled = false;

        config.mode.packets.enabled = true;
        config.mode.packets.clear_on_start = false;
        config.mode.packets.clear_interval = 10;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ClearPacketNoScanTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();
        let fee_denom_a = MonoTagged::new(Denom::base(
            &config.native_tokens[0],
            &config.native_tokens[0],
        ));

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let amount1 = random_u128_range(1000, 5000);

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(amount1).as_ref(),
        )?;

        let denom_b2 = derive_ibc_denom(
            &chains.node_b.chain_driver().value().chain_type,
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        thread::sleep(Duration::from_secs(5));

        relayer.with_supervisor(|| {
            info!("Assert clear on start does not trigger");
            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &(balance_a.clone() - amount1).as_ref(),
            )?;

            // Clear on start is disabled, packets will not be cleared
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(0u128).as_ref(),
            )?;

            // Wait for clear interval to trigger
            thread::sleep(Duration::from_secs(20));

            info!("Assert clear interval does not trigger");

            // Channel is not discovered, packets won't be cleared
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(0u128).as_ref(),
            )?;

            info!("Trigger a transfer");

            let dst_height = chains.handle_b().query_latest_height()?;

            // Trigger a transfer from chain
            chains.node_a.chain_driver().transfer_from_chain(
                &chains.node_a.wallets().user1(),
                &chains.node_b.wallets().user1().address(),
                &channel.port_a.0,
                &channel.channel_id_a.0,
                &denom_a.with_amount(amount1).as_ref(),
                &fee_denom_a.with_amount(381000000u64).as_ref(),
                &dst_height,
            )?;

            info!("Assert clear interval correctly triggers");

            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &(balance_a - amount1 - amount1).as_ref(),
            )?;

            // Wait for clear interval to clear packets
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(amount1 + amount1).as_ref(),
            )?;

            Ok(())
        })
    }
}

impl TestOverrides for ClearPacketOverrideTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        // Disabling client workers and clear_on_start should make the relayer not
        // relay any packet it missed before starting.
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
        config.mode.channels.enabled = false;

        config.mode.packets.enabled = true;
        config.mode.packets.clear_on_start = false;
        // Set a very high global clear interval
        config.mode.packets.clear_interval = 10000;

        for chain_config in config.chains.iter_mut() {
            match chain_config {
                // Use a small clear interval in the chain configurations to override the global high interval
                ChainConfig::CosmosSdk(chain_config) | ChainConfig::Namada(chain_config) => {
                    chain_config.clear_interval = Some(10)
                }
            }
        }
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ClearPacketOverrideTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();
        let fee_denom_a = MonoTagged::new(Denom::base(
            &config.native_tokens[0],
            &config.native_tokens[0],
        ));

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let amount1 = random_u128_range(1000, 5000);

        let balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(amount1).as_ref(),
        )?;

        let denom_b2 = derive_ibc_denom(
            &chains.node_b.chain_driver().value().chain_type,
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &denom_a,
        )?;

        thread::sleep(Duration::from_secs(5));

        relayer.with_supervisor(|| {
            info!("Assert clear on start does not trigger");
            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &(balance_a.clone() - amount1).as_ref(),
            )?;

            // Clear on start is disabled, packets will not be cleared
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(0u128).as_ref(),
            )?;

            // Wait for clear interval to trigger
            thread::sleep(Duration::from_secs(20));

            info!("Assert clear interval does not trigger");

            // Channel is not discovered, packets won't be cleared
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(0u128).as_ref(),
            )?;

            info!("Trigger a transfer");

            let dst_height = chains.handle_b().query_latest_height()?;

            // Trigger a transfer from chain
            chains.node_a.chain_driver().transfer_from_chain(
                &chains.node_a.wallets().user1(),
                &chains.node_b.wallets().user1().address(),
                &channel.port_a.0,
                &channel.channel_id_a.0,
                &denom_a.with_amount(amount1).as_ref(),
                &fee_denom_a.with_amount(381000000u64).as_ref(),
                &dst_height,
            )?;

            info!("Assert clear interval correctly triggers");

            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &(balance_a - amount1 - amount1).as_ref(),
            )?;

            // Wait for clear interval to clear packets
            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_b2.with_amount(amount1 + amount1).as_ref(),
            )?;

            Ok(())
        })
    }
}

impl TestOverrides for ClearPacketSequencesTest {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

use ibc_relayer::link::{Link, LinkParameters};

impl BinaryChannelTest for ClearPacketSequencesTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        const NUM_TRANSFERS: usize = 20;
        let packet_config = relayer.config.mode.packets;

        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let amount = denom_a.with_amount(random_u128_range(1000, 5000));

        info!("Performing {NUM_TRANSFERS} IBC transfer, which should *not* be relayed");

        chains.node_a.chain_driver().ibc_transfer_token_multiple(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &amount.as_ref(),
            NUM_TRANSFERS,
            None,
        )?;

        sleep(Duration::from_secs(5));

        let channel_end_a = query_identified_channel_end(
            chains.handle_a(),
            channel.channel_id_a.as_ref(),
            channel.port_a.as_ref(),
        )?;

        let pending_packets_a =
            pending_packet_summary(chains.handle_a(), chains.handle_b(), channel_end_a.value())?;

        info!("Pending packets: {:?}", pending_packets_a);

        assert_eq!(pending_packets_a.unreceived_packets.len(), NUM_TRANSFERS);

        let opts = LinkParameters {
            src_port_id: channel.port_a.clone().into_value(),
            src_channel_id: channel.channel_id_a.clone().into_value(),
            max_memo_size: packet_config.ics20_max_memo_size,
            max_receiver_size: packet_config.ics20_max_receiver_size,
        };

        // Clear all even packets
        let to_clear = pending_packets_a
            .unreceived_packets
            .iter()
            .filter(|seq| seq.as_u64() % 2 == 0)
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        info!("Packets to clear: {:?}", to_clear);

        let link = Link::new_from_opts(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            opts,
            false,
            false,
        )?;

        info!("Clearing all even packets ({})", to_clear.len());

        link.relay_recv_packet_and_timeout_messages(to_clear)
            .unwrap();

        sleep(Duration::from_secs(10));

        let pending_packets =
            pending_packet_summary(chains.handle_a(), chains.handle_b(), channel_end_a.value())?;

        info!("Pending packets: {pending_packets:?}");

        assert_eq!(pending_packets.unreceived_packets.len(), NUM_TRANSFERS / 2);
        assert_eq!(pending_packets.unreceived_acks.len(), NUM_TRANSFERS / 2);

        let to_clear = pending_packets
            .unreceived_acks
            .iter()
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        info!("Packets to clear: {to_clear:?}");

        info!("Clearing all unreceived ack packets ({})", to_clear.len());

        let rev_link = link.reverse(false, false).unwrap();
        rev_link.relay_ack_packet_messages(to_clear).unwrap();

        let pending_packets_a =
            pending_packet_summary(chains.handle_a(), chains.handle_b(), channel_end_a.value())?;

        info!("Pending packets: {pending_packets_a:?}");

        assert_eq!(pending_packets_a.unreceived_acks.len(), 0);
        assert_eq!(
            pending_packets_a.unreceived_packets.len(),
            NUM_TRANSFERS / 2
        );

        info!(
            "Successfully cleared all even packets, remains {} odd packets",
            pending_packets_a.unreceived_packets.len()
        );

        Ok(())
    }
}
