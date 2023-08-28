//! Tests the successful channel upgrade:
//!
//! - `ChannelUpgradeManualHandshake` tests each step of the channel upgrade manually,
//!   without relaying on the supervisor.

use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics04_channel::version::Version;
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

pub struct ChannelUpgradeManualHandshake;

impl TestOverrides for ChannelUpgradeManualHandshake {
    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

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
        let new_ordering = None;
        let new_connection_hops = None;

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
            old_connection_hops_a,
            old_connection_hops_b,
        );

        info!("Will run ChanUpgradeInit step...");

        channel.flipped().build_chan_upgrade_init_and_send(
            Some(new_version),
            new_ordering,
            new_connection_hops,
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
