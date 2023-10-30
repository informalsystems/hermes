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

use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_test_framework::chain::config::{set_max_deposit_period, set_voting_period};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::{
    assert_eventually_channel_established, assert_eventually_channel_upgrade_ack,
    assert_eventually_channel_upgrade_confirm, assert_eventually_channel_upgrade_init,
    assert_eventually_channel_upgrade_open, assert_eventually_channel_upgrade_try,
    ChannelUpgradableAttributes,
};

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
        );

        let interm_attrs = ChannelUpgradableAttributes::new(
            old_version,
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
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
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
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
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
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
        );

        let interm_attrs = ChannelUpgradableAttributes::new(
            old_version,
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b.clone(),
        );

        let upgraded_attrs = ChannelUpgradableAttributes::new(
            new_version.clone(),
            new_version.clone(),
            old_ordering,
            old_connection_hops_a.clone(),
            old_connection_hops_b,
        );

        info!("Will initialise upgrade handshake with governance proposal...");

        chains.node_a.chain_driver().initialise_channel_upgrade(
            channel.src_port_id().as_str(),
            channel.src_channel_id().unwrap().as_str(),
            old_ordering.as_str(),
            old_connection_hops_a.first().unwrap().as_str(),
            &serde_json::to_string(&new_version.0).unwrap(),
            chains.handle_a().get_signer().unwrap().as_ref(),
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
