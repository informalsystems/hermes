//! This test tests TODO different cases:
//!
//! - The `IbcForwardTimeoutTransferTest` tests the case a timedout packet before being
//!   forwarded.
//!
//! - The `IbcForwardHopTimeoutTransferTest` tests the case a timedout packet after the first
//!   hop being forwarded.

use ibc_relayer::chain::counterparty::pending_packet_summary;
use ibc_relayer::chain::requests::Paginate;
use ibc_relayer::config::{self, ModeConfig};
use ibc_relayer::link::Link;
use ibc_relayer::link::LinkParameters;
use ibc_relayer_types::events::IbcEventType;
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::query_identified_channel_end;

use crate::tests::forward::memo::{HopMemoField, MemoField, MemoInfo};

#[test]
fn test_ibc_forward_timeout_transfer() -> Result<(), Error> {
    run_nary_channel_test(&IbcForwardTimeoutTransferTest {
        timeout_in_ns: 30000000000, // 30 seconds
        should_timeout: true,
    })
}

#[test]
fn test_ibc_forward_no_timeout_transfer() -> Result<(), Error> {
    run_nary_channel_test(&IbcForwardTimeoutTransferTest {
        timeout_in_ns: 90000000000, // 90 seconds
        should_timeout: false,
    })
}

#[test]
fn test_ibc_forward_hop_timeout_transfer() -> Result<(), Error> {
    run_nary_channel_test(&IbcForwardHopTimeoutTransferTest)
}

struct IbcForwardTimeoutTransferTestOverrides;

impl TestOverrides for IbcForwardTimeoutTransferTestOverrides {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            connections: config::Connections { enabled: false },
            channels: config::Channels { enabled: false },
            ..Default::default()
        };

        config.mode.clients.misbehaviour = false;
    }

    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl PortsOverride<3> for IbcForwardTimeoutTransferTestOverrides {}

struct IbcForwardHopTimeoutTransferTestOverrides;

impl TestOverrides for IbcForwardHopTimeoutTransferTestOverrides {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            connections: config::Connections { enabled: false },
            channels: config::Channels { enabled: false },
            ..Default::default()
        };

        config.mode.clients.misbehaviour = false;
    }

    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl PortsOverride<4> for IbcForwardHopTimeoutTransferTestOverrides {}

struct IbcForwardTimeoutTransferTest {
    pub timeout_in_ns: u64,
    pub should_timeout: bool,
}

impl NaryChannelTest<3> for IbcForwardTimeoutTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 3>,
        channels: NaryConnectedChannels<Handle, 3>,
    ) -> Result<(), Error> {
        let packet_config = relayer.config.mode.packets;

        let connected_chains = chains.connected_chains_at::<0, 1>()?;

        let node_a = chains.full_node_at::<0>()?;
        let node_b = chains.full_node_at::<1>()?;
        let node_c = chains.full_node_at::<2>()?;

        let handle_a = chains.chain_handle_at::<0>()?;
        let handle_b = chains.chain_handle_at::<1>()?;
        let handle_c = chains.chain_handle_at::<2>()?;

        let channel_a_to_b = channels.channel_at::<0, 1>()?;
        let channel_b_to_c = channels.channel_at::<1, 2>()?;

        let denom_a = connected_chains.node_a.denom();

        let denom_b = derive_ibc_denom(
            &node_b.chain_driver().value().chain_type,
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let denom_a_to_b = derive_ibc_denom(
            &node_b.chain_driver().value().chain_type,
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let denom_a_to_c = derive_ibc_denom(
            &node_c.chain_driver().value().chain_type,
            &channel_b_to_c.port_b.as_ref(),
            &channel_b_to_c.channel_id_b.as_ref(),
            &denom_b.as_ref(),
        )?;

        let wallets_a = node_a.wallets();
        let wallet_a = wallets_a.user1();

        let wallets_b = node_b.wallets();
        let wallet_b = wallets_b.user1();

        let wallets_c = node_c.wallets();
        let wallet_c = wallets_c.user1();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_c_amount = 4000_u128;

        let memo_field: MemoField<MemoInfo> = MemoField::new(
            wallet_c.address().value().to_string(),
            channel_b_to_c.port_a.to_string(),
            channel_b_to_c.channel.a_channel_id().unwrap().to_string(),
            self.timeout_in_ns,
        );
        let memo = serde_json::to_string(&memo_field).unwrap();

        node_a
            .chain_driver()
            .ibc_transfer_token_with_memo_and_timeout(
                &channel_a_to_b.port_a.as_ref(),
                &channel_a_to_b.channel_id_a.as_ref(),
                &wallet_a,
                &wallet_b.address(),
                &denom_a.with_amount(a_to_c_amount).as_ref(),
                Some(memo),
                Some(Duration::from_secs(50)),
            )?;

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a.clone() - a_to_c_amount).as_ref(),
        )?;

        // Wait for packet to timeout
        std::thread::sleep(Duration::from_secs(35));

        let channel_end_a = query_identified_channel_end(
            &handle_a,
            channel_a_to_b.channel_id_a.as_ref(),
            channel_a_to_b.port_a.as_ref(),
        )?;

        let pending_packets_a =
            pending_packet_summary(&handle_a, &handle_b, channel_end_a.value(), Paginate::All)?;

        let to_clear = pending_packets_a
            .unreceived_packets
            .iter()
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        let opts = LinkParameters {
            src_port_id: channel_a_to_b.port_a.clone().into_value(),
            src_channel_id: channel_a_to_b.channel_id_a.clone().into_value(),
            max_memo_size: packet_config.ics20_max_memo_size,
            max_receiver_size: packet_config.ics20_max_receiver_size,
            exclude_src_sequences: vec![],
        };

        let link = Link::new_from_opts(handle_a, handle_b.clone(), opts, false, false)?;

        assert!(
            to_clear.len() == 1,
            "expected exactly one packet to clear from A to B"
        );

        let result = link
            .relay_recv_packet_and_timeout_messages(to_clear)
            .unwrap();

        assert!(
            result
                .iter()
                .any(|event| event.event_type() == IbcEventType::SendPacket),
            "expected to relay send packet from A to B"
        );

        // Wait for packet to timeout
        std::thread::sleep(Duration::from_secs(35));

        let channel_end_b = query_identified_channel_end(
            &handle_b,
            channel_b_to_c.channel_id_a.as_ref(),
            channel_b_to_c.port_a.as_ref(),
        )?;

        let pending_packets_b =
            pending_packet_summary(&handle_b, &handle_c, channel_end_b.value(), Paginate::All)?;

        let to_clear = pending_packets_b
            .unreceived_packets
            .iter()
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        assert!(
            to_clear.len() == 1,
            "expected exactly one packet to clear from B to C"
        );

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a.clone() - a_to_c_amount).as_ref(),
        )?;

        info!(
            "waiting for user on chain A to be refunded the amount of {}",
            a_to_c_amount
        );

        relayer.with_supervisor(||{
            if self.should_timeout{
                node_a
                    .chain_driver()
                    .assert_eventual_wallet_amount(&wallet_a.address(), &balance_a.as_ref())?;

                node_c.chain_driver().assert_eventual_wallet_amount(
                    &wallet_c.address(),
                    &denom_a_to_c.with_amount(0u128).as_ref(),
                )?;
            } else {
                node_a
                    .chain_driver()
                    .assert_eventual_wallet_amount(&wallet_a.address(), &(balance_a.clone() - a_to_c_amount).as_ref())?;

                node_c.chain_driver().assert_eventual_wallet_amount(
                    &wallet_c.address(),
                    &denom_a_to_c.with_amount(a_to_c_amount).as_ref(),
                )?;
            }

            node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_a_to_b.with_amount(0_u128).as_ref(),
            )?;

            info!(
                "successfully performed IBC timeout transfer for PFM transfer from chain {} to chain {}",
                chains.chain_handle_at::<0>().unwrap().value(),
                chains.chain_handle_at::<2>().unwrap().value(),
            );

            Ok(())
        })?;

        let pending_packets_b =
            pending_packet_summary(&handle_b, &handle_c, channel_end_b.value(), Paginate::All)?;

        let to_clear = pending_packets_b
            .unreceived_packets
            .iter()
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        assert!(
            to_clear.is_empty(),
            "expected all packets to have been cleared from B to C"
        );

        Ok(())
    }
}

struct IbcForwardHopTimeoutTransferTest;

impl NaryChannelTest<4> for IbcForwardHopTimeoutTransferTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 4>,
        channels: NaryConnectedChannels<Handle, 4>,
    ) -> Result<(), Error> {
        let packet_config = relayer.config.mode.packets;

        let connected_chains = chains.connected_chains_at::<0, 1>()?;

        let node_a = chains.full_node_at::<0>()?;
        let node_b = chains.full_node_at::<1>()?;
        let node_c = chains.full_node_at::<2>()?;
        let node_d = chains.full_node_at::<3>()?;

        let handle_a = chains.chain_handle_at::<0>()?;
        let handle_b = chains.chain_handle_at::<1>()?;
        let handle_c = chains.chain_handle_at::<2>()?;

        let channel_a_to_b = channels.channel_at::<0, 1>()?;
        let channel_b_to_c = channels.channel_at::<1, 2>()?;
        let channel_c_to_d = channels.channel_at::<2, 3>()?;

        let denom_a = connected_chains.node_a.denom();

        let denom_a_to_b = derive_ibc_denom(
            &node_b.chain_driver().value().chain_type,
            &channel_a_to_b.port_b.as_ref(),
            &channel_a_to_b.channel_id_b.as_ref(),
            &denom_a,
        )?;

        let denom_b_to_c = derive_ibc_denom(
            &node_c.chain_driver().value().chain_type,
            &channel_b_to_c.port_b.as_ref(),
            &channel_b_to_c.channel_id_b.as_ref(),
            &denom_a_to_b.as_ref(),
        )?;

        let denom_a_to_d = derive_ibc_denom(
            &node_d.chain_driver().value().chain_type,
            &channel_c_to_d.port_b.as_ref(),
            &channel_c_to_d.channel_id_b.as_ref(),
            &denom_b_to_c.as_ref(),
        )?;

        let wallets_a = node_a.wallets();
        let wallet_a = wallets_a.user1();

        let wallets_b = node_b.wallets();
        let wallet_b = wallets_b.user1();

        let wallets_c = node_c.wallets();
        let wallet_c = wallets_c.user1();

        let wallets_d = node_d.wallets();
        let wallet_d = wallets_d.user1();

        let balance_a = node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let a_to_d_amount = 4000_u128;

        let memo_field = HopMemoField::new(
            wallet_c.address().value().to_string(),
            channel_b_to_c.port_a.to_string(),
            channel_b_to_c.channel.a_channel_id().unwrap().to_string(),
            "20s".to_owned(),
            wallet_d.address().value().to_string(),
            channel_c_to_d.port_a.to_string(),
            channel_c_to_d.channel.a_channel_id().unwrap().to_string(),
            "20s".to_owned(),
        );
        let memo = serde_json::to_string(&memo_field).unwrap();

        node_a
            .chain_driver()
            .ibc_transfer_token_with_memo_and_timeout(
                &channel_a_to_b.port_a.as_ref(),
                &channel_a_to_b.channel_id_a.as_ref(),
                &wallet_a,
                &wallet_b.address(),
                &denom_a.with_amount(a_to_d_amount).as_ref(),
                Some(memo),
                Some(Duration::from_secs(300)),
            )?;

        std::thread::sleep(Duration::from_secs(30));

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a.clone() - a_to_d_amount).as_ref(),
        )?;

        // First hop transfer
        let channel_end_a = query_identified_channel_end(
            &handle_a,
            channel_a_to_b.channel_id_a.as_ref(),
            channel_a_to_b.port_a.as_ref(),
        )?;

        let pending_packets_a =
            pending_packet_summary(&handle_a, &handle_b, channel_end_a.value(), Paginate::All)?;

        let to_clear = pending_packets_a
            .unreceived_packets
            .iter()
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        let opts = LinkParameters {
            src_port_id: channel_a_to_b.port_a.clone().into_value(),
            src_channel_id: channel_a_to_b.channel_id_a.clone().into_value(),
            max_memo_size: packet_config.ics20_max_memo_size,
            max_receiver_size: packet_config.ics20_max_receiver_size,
            exclude_src_sequences: vec![],
        };

        let link = Link::new_from_opts(handle_a.clone(), handle_b.clone(), opts, false, false)?;

        info!("Clearing all packets ({})", to_clear.len());

        link.relay_recv_packet_and_timeout_messages(to_clear)
            .unwrap();

        node_a.chain_driver().assert_eventual_wallet_amount(
            &wallet_a.address(),
            &(balance_a.clone() - a_to_d_amount).as_ref(),
        )?;

        std::thread::sleep(Duration::from_secs(30));

        // Second hop transfer
        let channel_end_a = query_identified_channel_end(
            &handle_b,
            channel_b_to_c.channel_id_a.as_ref(),
            channel_b_to_c.port_a.as_ref(),
        )?;

        let pending_packets_a =
            pending_packet_summary(&handle_b, &handle_c, channel_end_a.value(), Paginate::All)?;

        let to_clear = pending_packets_a
            .unreceived_packets
            .iter()
            .map(|&seq| seq..=seq)
            .collect::<Vec<_>>();

        let opts = LinkParameters {
            src_port_id: channel_b_to_c.port_a.clone().into_value(),
            src_channel_id: channel_b_to_c.channel_id_a.clone().into_value(),
            max_memo_size: packet_config.ics20_max_memo_size,
            max_receiver_size: packet_config.ics20_max_receiver_size,
            exclude_src_sequences: vec![],
        };

        let link = Link::new_from_opts(handle_b, handle_c, opts, false, false)?;

        info!("Clearing all packets ({})", to_clear.len());

        link.relay_recv_packet_and_timeout_messages(to_clear)
            .unwrap();

        relayer.with_supervisor(|| {
            node_a
                .chain_driver()
                .assert_eventual_wallet_amount(&wallet_a.address(), &balance_a.as_ref())?;

            node_d.chain_driver().assert_eventual_wallet_amount(
                &wallet_d.address(),
                &denom_a_to_d.with_amount(0u128).as_ref(),
            )?;

            node_c.chain_driver().assert_eventual_wallet_amount(
                &wallet_c.address(),
                &denom_b_to_c.with_amount(0u128).as_ref(),
            )?;

            node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &denom_a_to_b.with_amount(0_u128).as_ref(),
            )?;

            info!(
                "successfully performed IBC timeout transfer for PFM transfer from chain {} to chain {}",
                chains.chain_handle_at::<0>().unwrap().value(),
                chains.chain_handle_at::<3>().unwrap().value(),
            );

            Ok(())
        })
    }
}

impl HasOverrides for IbcForwardTimeoutTransferTest {
    type Overrides = IbcForwardTimeoutTransferTestOverrides;

    fn get_overrides(&self) -> &IbcForwardTimeoutTransferTestOverrides {
        &IbcForwardTimeoutTransferTestOverrides
    }
}

impl HasOverrides for IbcForwardHopTimeoutTransferTest {
    type Overrides = IbcForwardHopTimeoutTransferTestOverrides;

    fn get_overrides(&self) -> &IbcForwardHopTimeoutTransferTestOverrides {
        &IbcForwardHopTimeoutTransferTestOverrides
    }
}
