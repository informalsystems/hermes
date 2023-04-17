use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::{
    ics02_client::height::Height,
    ics04_channel::{timeout::UpgradeTimeout, version::Version},
};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::{
    assert_eventually_channel_established, assert_eventually_channel_upgrade_init,
    init_channel_upgrade,
};

#[test]
fn test_channel_open_upgrade_handshake() -> Result<(), Error> {
    run_binary_channel_test(&ChannelOpenUpgradeHandshake)
}

pub struct ChannelOpenUpgradeHandshake;

impl TestOverrides for ChannelOpenUpgradeHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.connections.enabled = true;

        config.mode.channels.enabled = false;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ChannelOpenUpgradeHandshake {
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

        let old_version = channel_end_a.version;
        let old_ordering = channel_end_a.ordering;
        let old_connection_hops = channel_end_a.connection_hops;

        let channel = channels.channel;
        let new_version = Some(Version::ics20_with_fee());
        let assert_version = if let Some(version) = new_version.clone() {
            version
        } else {
            old_version.clone()
        };
        let new_ordering = None;
        let assert_ordering = if let Some(ordering) = new_ordering {
            ordering
        } else {
            old_ordering
        };
        let new_connection_hops = None;
        let assert_connection_hops = if let Some(connection_hops) = new_connection_hops.clone() {
            connection_hops
        } else {
            old_connection_hops.clone()
        };
        let height = Height::new(
            ChainId::chain_version(chains.chain_id_a().0.to_string().as_str()),
            60,
        )
        .map_err(|e| eyre!("error creating height for timeout height: {e}"))?;
        let timeout = UpgradeTimeout::new(Some(height), None)
            .map_err(|e| eyre!("error creating UpgradeTimeout: {e}"))?;

        info!("Initialise channel upgrade process...");

        let (channel_id_on_a, _channel_to_b_on_a) = init_channel_upgrade(
            &chains.handle_a,
            &chains.handle_b,
            channel,
            new_version,
            new_ordering,
            new_connection_hops,
            timeout,
        )?;

        info!("Check that channel A is in INITUPGRADE State and channel B in OPEN State");

        assert_eventually_channel_upgrade_init(
            &chains.handle_b,
            &chains.handle_a,
            &channel_id_on_a.as_ref(),
            &channels.port_b.as_ref(),
            &old_version,
            &old_ordering,
            &old_connection_hops,
            &assert_version,
            &assert_ordering,
            &assert_connection_hops,
        )?;

        Ok(())
    }
}
