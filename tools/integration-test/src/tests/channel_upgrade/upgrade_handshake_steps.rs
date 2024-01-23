//! Tests channel upgrade:
//!
//! - `ChannelUpgradeManualHandshake` tests each step of the channel upgrade manually,
//!   without relaying on the supervisor.
//!
//! - `ChannelUpgradeHandshakeFromTry` tests that the channel worker will finish the
//!   upgrade handshake if the channel is being upgraded and is at the Try step.
//!
//! - `ChannelUpgradeHandshakeFromAck` tests that the channel worker will finish the
//!   upgrade handshake if the channel is being upgraded and is at the Ack step.
//!
//! - `ChannelUpgradeHandshakeFromConfirm` tests that the channel worker will finish the
//!   upgrade handshake if the channel is being upgraded and is at the Confirm step.
//!
//! - `ChannelUpgradeHandshakeTimeoutOnAck` tests that the channel worker will cancel the
//!   upgrade handshake if the Ack step fails due to an upgrade timeout.
//!
//! - `ChannelUpgradeHandshakeTimeoutWhenFlushing` tests that the channel worker will timeout the
//!   upgrade handshake if the counterparty does not finish flushing the packets before the upgrade timeout.
//!
//! - `ChannelUpgradeHandshakeFlushPackets` tests that the channel worker will complete the
//!   upgrade handshake when packets need to be flushed during the handshake.
//!
//! - `ChannelUpgradeHandshakeInitiateNewUpgrade` tests that the channel worker will
//!   finish the upgrade handshake if the side that moved to `OPEN` initiates a
//!   new upgrade before the counterparty moved to `OPEN`.

use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics04_channel::channel::{State as ChannelState, UpgradeState};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::events::IbcEventType;
use ibc_test_framework::chain::config::{set_max_deposit_period, set_voting_period};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::{
    assert_eventually_channel_established, assert_eventually_channel_upgrade_ack,
    assert_eventually_channel_upgrade_cancel, assert_eventually_channel_upgrade_confirm,
    assert_eventually_channel_upgrade_flushing, assert_eventually_channel_upgrade_init,
    assert_eventually_channel_upgrade_open, assert_eventually_channel_upgrade_try,
    ChannelUpgradableAttributes,
};
use ibc_test_framework::util::random::random_u128_range;

#[test]
fn test_channel_upgrade_manual_handshake() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeManualHandshake)
}

#[test]
fn test_channel_upgrade_handshake_from_try() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeFromTry)
}

#[test]
fn test_channel_upgrade_handshake_from_ack() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeFromAck)
}

#[test]
fn test_channel_upgrade_handshake_from_confirm() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeFromConfirm)
}

#[test]
fn test_channel_upgrade_handshake_timeout_on_ack() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeTimeoutOnAck)
}

#[test]
fn test_channel_upgrade_handshake_timeout_when_flushing() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeTimeoutWhenFlushing)
}

#[test]
fn test_channel_upgrade_handshake_flush_packets() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeFlushPackets)
}

#[test]
fn test_channel_upgrade_handshake_initiate_new_upgrade() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeHandshakeInitiateNewUpgrade)
}

const MAX_DEPOSIT_PERIOD: &str = "10s";
const VOTING_PERIOD: u64 = 10;

struct ChannelUpgradeTestOverrides;

impl TestOverrides for ChannelUpgradeTestOverrides {
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        set_max_deposit_period(genesis, MAX_DEPOSIT_PERIOD)?;
        set_voting_period(genesis, VOTING_PERIOD)?;
        Ok(())
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        config.mode.clients.misbehaviour = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

struct ChannelUpgradeManualHandshake;

impl BinaryChannelTest for ChannelUpgradeManualHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let interm_attrs = ChannelUpgradableAttributes::new(
            old_version,
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
            Sequence::from(1),
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the step ChanUpgradeInit was correctly executed...");

        assert_eventually_channel_upgrade_init(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &old_attrs,
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        info!("Will run ChanUpgradeAck step...");

        channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck was correctly executed...");

        assert_eventually_channel_upgrade_ack(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            ChannelState::Flushcomplete,
            ChannelState::Flushing,
            &old_attrs,
        )?;

        info!("Will run ChanUpgradeConfirm step...");

        channel.build_chan_upgrade_confirm_and_send()?;

        info!("Check that the step ChanUpgradeConfirm was correctly executed...");

        assert_eventually_channel_upgrade_confirm(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &interm_attrs.flipped(),
        )?;

        info!("Will run ChanUpgradeOpen step...");

        channel.flipped().build_chan_upgrade_open_and_send()?;

        info!("Check that the ChanUpgradeOpen steps were correctly executed...");

        // This will assert that both channel ends are eventually
        // in Open state, and that the fields targeted by the upgrade
        // have been correctly updated.
        assert_eventually_channel_upgrade_open(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &upgraded_attrs,
        )?;

        Ok(())
    }
}

struct ChannelUpgradeHandshakeFromTry;

impl BinaryChannelTest for ChannelUpgradeHandshakeFromTry {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
            Sequence::from(1),
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        info!("Check that the channel upgrade successfully upgraded the version...");

        relayer.with_supervisor(|| {
            // This will assert that both channel ends are eventually
            // in Open state, and that the fields targeted by the upgrade
            // have been correctly updated.
            assert_eventually_channel_upgrade_open(
                &chains.handle_a,
                &chains.handle_b,
                &channels.channel_id_a.as_ref(),
                &channels.port_a.as_ref(),
                &upgraded_attrs,
            )?;

            Ok(())
        })
    }
}

struct ChannelUpgradeHandshakeFromAck;

impl BinaryChannelTest for ChannelUpgradeHandshakeFromAck {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
            Sequence::from(1),
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        info!("Will run ChanUpgradeAck step...");

        channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck was correctly executed...");

        assert_eventually_channel_upgrade_ack(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            ChannelState::Flushcomplete,
            ChannelState::Flushing,
            &old_attrs,
        )?;

        info!("Check that the channel upgrade successfully upgraded the version...");

        relayer.with_supervisor(|| {
            // This will assert that both channel ends are eventually
            // in Open state, and that the fields targeted by the upgrade
            // have been correctly updated.
            assert_eventually_channel_upgrade_open(
                &chains.handle_a,
                &chains.handle_b,
                &channels.channel_id_a.as_ref(),
                &channels.port_a.as_ref(),
                &upgraded_attrs,
            )?;

            Ok(())
        })
    }
}
struct ChannelUpgradeHandshakeFromConfirm;

impl BinaryChannelTest for ChannelUpgradeHandshakeFromConfirm {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let interm_attrs = ChannelUpgradableAttributes::new(
            old_version,
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
            Sequence::from(1),
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        info!("Will run ChanUpgradeAck step...");

        channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck was correctly executed...");

        assert_eventually_channel_upgrade_ack(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            ChannelState::Flushcomplete,
            ChannelState::Flushing,
            &old_attrs,
        )?;

        info!("Will run ChanUpgradeConfirm step...");

        channel.build_chan_upgrade_confirm_and_send()?;

        info!("Check that the step ChanUpgradeConfirm was correctly executed...");

        assert_eventually_channel_upgrade_confirm(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &interm_attrs.flipped(),
        )?;

        info!("Check that the channel upgrade successfully upgraded the version...");

        relayer.with_supervisor(|| {
            // This will assert that both channel ends are eventually
            // in Open state, and that the fields targeted by the upgrade
            // have been correctly updated.
            assert_eventually_channel_upgrade_open(
                &chains.handle_a,
                &chains.handle_b,
                &channels.channel_id_a.as_ref(),
                &channels.port_a.as_ref(),
                &upgraded_attrs,
            )?;

            Ok(())
        })
    }
}

struct ChannelUpgradeHandshakeTimeoutOnAck;

impl BinaryChannelTest for ChannelUpgradeHandshakeTimeoutOnAck {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        info!("Will update channel params to set a short upgrade timeout...");

        chains.node_b.chain_driver().update_channel_params(
            5000000000,
            chains.handle_b().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the step ChanUpgradeInit was correctly executed...");

        assert_eventually_channel_upgrade_init(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &old_attrs,
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        // wait enough time so that ACK fails due to upgrade timeout
        sleep(Duration::from_secs(10));

        info!("Will run ChanUpgradeAck step...");

        let ack_event = channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck timed out...");

        // ACK should fail because the upgrade has timed out
        assert!(
            ack_event.is_none(),
            "channel upgrade ack should have failed due to timeout"
        );

        info!("Will run ChanUpgradeCancel step...");

        // Since the following assertion checks that the fields of channel ends
        // have not been updated, asserting there is a `UpgradeCancelChannel` event
        // avoids having a passing test due to the Upgrade Init step failing
        let cancel_event = channel.build_chan_upgrade_cancel_and_send()?;
        assert_eq!(
            cancel_event.event_type(),
            IbcEventType::UpgradeCancelChannel
        );

        info!("Check that the step ChanUpgradeCancel was correctly executed...");

        assert_eventually_channel_upgrade_cancel(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        Ok(())
    }
}

struct ChannelUpgradeHandshakeTimeoutWhenFlushing;

impl BinaryChannelTest for ChannelUpgradeHandshakeTimeoutWhenFlushing {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        info!("Will update channel params to set a shorter upgrade timeout...");

        // the upgrade timeout should be long enough for chain a
        // to complete Ack successfully so that it goes into `FLUSHING`
        chains.node_b.chain_driver().update_channel_params(
            25000000000,
            chains.handle_b().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the step ChanUpgradeInit was correctly executed...");

        assert_eventually_channel_upgrade_init(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &old_attrs,
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        // send a IBC transfer message from chain a to chain b
        // so that we have an in-flight packet and chain a
        // will move to `FLUSHING` during Ack
        let denom_a = chains.node_a.denom();
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();
        let a_to_b_amount = random_u128_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channels.port_a.as_ref(),
            &channels.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        info!("Will run ChanUpgradeAck step...");

        channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck was correctly executed...");

        assert_eventually_channel_upgrade_flushing(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &old_attrs,
        )?;

        // wait enough time so that timeout expires while chain a is in FLUSHING
        sleep(Duration::from_nanos(35000000000));

        info!("Will run ChanUpgradeTimeout step...");

        // Since the chain a has not moved to `FLUSH_COMPLETE` before the upgrade timeout
        // expired, then we can submit `MsgChannelUpgradeTimeout` on chain b
        // to cancel the upgrade and move the channel back to `OPEN`
        let timeout_event = channel.build_chan_upgrade_timeout_and_send()?;
        assert_eq!(
            timeout_event.event_type(),
            IbcEventType::UpgradeTimeoutChannel
        );

        let cancel_event = channel.flipped().build_chan_upgrade_cancel_and_send()?;
        assert_eq!(
            cancel_event.event_type(),
            IbcEventType::UpgradeCancelChannel
        );

        info!("Check that the step ChanUpgradeTimeout was correctly executed...");

        assert_eventually_channel_upgrade_cancel(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        Ok(())
    }
}

struct ChannelUpgradeHandshakeFlushPackets;

impl BinaryChannelTest for ChannelUpgradeHandshakeFlushPackets {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

        let old_attrs = ChannelUpgradableAttributes::new(
            old_version.clone(),
            old_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
            Sequence::from(1),
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the step ChanUpgradeInit was correctly executed...");

        assert_eventually_channel_upgrade_init(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &old_attrs,
        )?;

        // send a IBC transfer message from chain a to chain b
        // so that we have an in-flight packet and chain a
        // will move to `FLUSHING` during Ack
        let denom_a = chains.node_a.denom();
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();
        let a_to_b_amount = random_u128_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_a(),
            chains.chain_id_b(),
            a_to_b_amount,
            denom_a
        );

        chains.node_a.chain_driver().ibc_transfer_token(
            &channels.port_a.as_ref(),
            &channels.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(a_to_b_amount).as_ref(),
        )?;

        // send a IBC transfer message from chain b to chain a
        // so that we have an in-flight packet and chain a
        // will move to `FLUSHING` during Try
        let denom_b = chains.node_b.denom();
        let b_to_a_amount = random_u128_range(1000, 5000);

        info!(
            "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
            chains.chain_id_b(),
            chains.chain_id_a(),
            b_to_a_amount,
            denom_b
        );

        chains.node_b.chain_driver().ibc_transfer_token(
            &channels.port_b.as_ref(),
            &channels.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_a.address(),
            &denom_b.with_amount(b_to_a_amount).as_ref(),
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &old_attrs.flipped(),
        )?;

        info!("Will run ChanUpgradeAck step...");

        channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck was correctly executed...");

        // channel a is `FLUSHING` because the packet
        // from a to b has not been cleared yet
        assert_eventually_channel_upgrade_ack(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            ChannelState::Flushing,
            ChannelState::Flushing,
            &old_attrs,
        )?;

        info!("Check that the channel upgrade successfully upgraded the version...");

        // start supervisor to clear in-flight packets
        // and move channel ends to `FLUSH_COMPLETE`
        relayer.with_supervisor(|| {
            let ibc_denom_a = derive_ibc_denom(
                &channels.port_a.as_ref(),
                &channels.channel_id_a.as_ref(),
                &denom_b,
            )?;

            chains.node_a.chain_driver().assert_eventual_wallet_amount(
                &wallet_a.address(),
                &ibc_denom_a.with_amount(b_to_a_amount).as_ref(),
            )?;

            let ibc_denom_b = derive_ibc_denom(
                &channels.port_b.as_ref(),
                &channels.channel_id_b.as_ref(),
                &denom_a,
            )?;

            chains.node_b.chain_driver().assert_eventual_wallet_amount(
                &wallet_b.address(),
                &ibc_denom_b.with_amount(a_to_b_amount).as_ref(),
            )?;

            // This will assert that both channel ends are eventually
            // in Open state, and that the fields targeted by the upgrade
            // have been correctly updated.
            assert_eventually_channel_upgrade_open(
                &chains.handle_a,
                &chains.handle_b,
                &channels.channel_id_a.as_ref(),
                &channels.port_a.as_ref(),
                &upgraded_attrs,
            )?;

            Ok(())
        })
    }
}

struct ChannelUpgradeHandshakeInitiateNewUpgrade;

impl BinaryChannelTest for ChannelUpgradeHandshakeInitiateNewUpgrade {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!("Check that channels are both in OPEN State");

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
        )?;

        let mut channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let mut channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        let pre_upgrade_1_version = channel_end_a.version;
        let pre_upgrade_1_ordering = channel_end_a.ordering;
        let pre_upgrade_1_connection_hops_a = channel_end_a.connection_hops.clone();
        let pre_upgrade_1_connection_hops_b = channel_end_b.connection_hops.clone();

        let channel = channels.channel;
        let post_upgrade_1_version = Version::ics20_with_fee();

        let pre_upgrade_1_attrs = ChannelUpgradableAttributes::new(
            pre_upgrade_1_version.clone(),
            pre_upgrade_1_version.clone(),
            pre_upgrade_1_ordering,
            pre_upgrade_1_connection_hops_a.clone(),
            pre_upgrade_1_connection_hops_b.clone(),
            Sequence::from(1),
        );

        let interm_upgrade_1_attrs = ChannelUpgradableAttributes::new(
            pre_upgrade_1_version,
            post_upgrade_1_version.clone(),
            pre_upgrade_1_ordering,
            pre_upgrade_1_connection_hops_a.clone(),
            pre_upgrade_1_connection_hops_b.clone(),
            Sequence::from(1),
        );

        info!("Will initialise on chain A upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            pre_upgrade_1_ordering.as_str(),
            pre_upgrade_1_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&post_upgrade_1_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the step ChanUpgradeInit was correctly executed...");

        assert_eventually_channel_upgrade_init(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            &pre_upgrade_1_attrs,
        )?;

        info!("Will run ChanUpgradeTry step...");

        channel.build_chan_upgrade_try_and_send()?;

        info!("Check that the step ChanUpgradeTry was correctly executed...");

        assert_eventually_channel_upgrade_try(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &pre_upgrade_1_attrs.flipped(),
        )?;

        info!("Will run ChanUpgradeAck step...");

        channel.flipped().build_chan_upgrade_ack_and_send()?;

        info!("Check that the step ChanUpgradeAck was correctly executed...");

        assert_eventually_channel_upgrade_ack(
            &chains.handle_a,
            &chains.handle_b,
            &channels.channel_id_a.as_ref(),
            &channels.port_a.as_ref(),
            ChannelState::Flushcomplete,
            ChannelState::Flushing,
            &pre_upgrade_1_attrs,
        )?;

        info!("Will run ChanUpgradeConfirm step...");

        channel.build_chan_upgrade_confirm_and_send()?;

        info!("Check that the step ChanUpgradeConfirm was correctly executed...");

        assert_eventually_channel_upgrade_confirm(
            &chains.handle_b,
            &chains.handle_a,
            &channels.channel_id_b.as_ref(),
            &channels.port_b.as_ref(),
            &interm_upgrade_1_attrs.flipped(),
        )?;

        // ChannelEnd B is now `OPEN` (because both ends did not have in-flight packets)
        // Initialise a new upgrade handshake on chain B before ChannelEnd A moves to `OPEN`

        let pre_upgrade_2_ordering = channel_end_a.ordering;
        let pre_upgrade_2_connection_hops_b = channel_end_b.connection_hops.clone();

        let post_upgrade_2_version = Version::ics20();

        info!("Will initialise on chain B upgrade handshake with governance proposal...");

        chains.node_b.chain_driver().initialise_channel_upgrade(
            channel.dst_port_id().as_str(),
            channel.dst_channel_id().unwrap().as_str(),
            pre_upgrade_2_ordering.as_str(),
            pre_upgrade_2_connection_hops_b.first().unwrap().as_str(),
            &serde_json::to_string(&post_upgrade_2_version.0).unwrap(),
            chains.handle_b().get_signer().unwrap().as_ref(),
            "1",
        )?;

        info!("Check that the step ChanUpgradeInit was correctly executed...");

        channel_end_b = chains
            .handle_b
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_b.0.clone(),
                    channel_id: channels.channel_id_b.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd B: {e}"))?;

        // upgrade sequence should have been incremented
        let upgrade_sequence_b = Sequence::from(2);
        if assert_eq!(channel_end_b.upgrade_sequence, upgrade_sequence_b) {
            return Err(Error::generic(eyre!(
                "expected channel end B upgrade sequence to be `{}`, but it is instead `{}`",
                upgrade_sequence_b,
                channel_end_b.upgrade_sequence
            )));
        }

        // Finish upgrade 1 on ChannelEnd A

        info!("Will run ChanUpgradeOpen step...");

        channel.flipped().build_chan_upgrade_open_and_send()?;

        info!("Check that the step ChanUpgradeOpen was correctly executed...");

        channel_end_a = chains
            .handle_a
            .query_channel(
                QueryChannelRequest {
                    port_id: channels.port_a.0.clone(),
                    channel_id: channels.channel_id_a.0.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(channel_end, _)| channel_end)
            .map_err(|e| eyre!("Error querying ChannelEnd A: {e}"))?;

        let state_a = ChannelState::Open(UpgradeState::NotUpgrading);
        if channel_end_a.state_matches(&state_a) {
            return Err(Error::generic(eyre!(
                "expected channel end A state to be `{}`, but is instead `{}`",
                state_a,
                channel_end_a.state()
            )));
        }

        if assert_eq!(channel_end_a.version(), post_upgrade_1_version) {
            return Err(Error::generic(eyre!(
                "expected channel end A version to be `{}`, but is instead `{}`",
                post_upgrade_1_version,
                channel_end_a.version()
            )));
        }

        Ok(())
    }
}

impl HasOverrides for ChannelUpgradeManualHandshake {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeFromTry {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeFromAck {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeFromConfirm {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeTimeoutOnAck {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeTimeoutWhenFlushing {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeFlushPackets {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}

impl HasOverrides for ChannelUpgradeHandshakeInitiateNewUpgrade {
    type Overrides = ChannelUpgradeTestOverrides;

    fn get_overrides(&self) -> &ChannelUpgradeTestOverrides {
        &ChannelUpgradeTestOverrides
    }
}
