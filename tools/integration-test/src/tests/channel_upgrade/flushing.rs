//! Tests that the relayer correctly flushes in-flight packets during channel upgrade.
//!

use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_test_framework::chain::config::{set_max_deposit_period, set_voting_period};
use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::channel::{
    assert_eventually_channel_established, assert_eventually_channel_upgrade_open,
    ChannelUpgradableAttributes,
};
use ibc_test_framework::util::random::random_u128_range;

#[test]
fn test_channel_upgrade_simple_flushing() -> Result<(), Error> {
    run_binary_channel_test(&ChannelUpgradeFlushing)
}

const MAX_DEPOSIT_PERIOD: &str = "10s";
const VOTING_PERIOD: u64 = 10;

pub struct ChannelUpgradeFlushing;

impl TestOverrides for ChannelUpgradeFlushing {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;
        config.mode.packets.auto_register_counterparty_payee = true;
        config.mode.packets.clear_interval = 0;
        config.mode.packets.clear_on_start = true;

        config.mode.clients.misbehaviour = false;
    }

    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        set_max_deposit_period(genesis, MAX_DEPOSIT_PERIOD)?;
        set_voting_period(genesis, VOTING_PERIOD)?;
        Ok(())
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for ChannelUpgradeFlushing {
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

        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();

        let denom_a = chains.node_a.denom();

        let port_a = channels.port_a.as_ref();
        let channel_id_a = channels.channel_id_a.as_ref();

        let wallets_a = chains.node_a.wallets();
        let wallets_b = chains.node_b.wallets();

        let user_a = wallets_a.user1();
        let user_b = wallets_b.user1();

        let send_amount = random_u128_range(1000, 2000);

        chain_driver_a.ibc_transfer_token(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
        )?;

        sleep(Duration::from_secs(3));

        chain_driver_a.ibc_transfer_token(
            &port_a,
            &channel_id_a,
            &user_a,
            &user_b.address(),
            &denom_a.with_amount(send_amount).as_ref(),
        )?;

        let old_ordering = channel_end_a.ordering;
        let old_connection_hops_a = channel_end_a.connection_hops;
        let old_connection_hops_b = channel_end_b.connection_hops;

        let channel = channels.channel;
        let new_version = Version::ics20_with_fee();

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

        sleep(Duration::from_secs(5));

        info!("Check that the channel upgrade successfully upgraded the version...");

        relayer.with_supervisor(|| {
            let denom_b = derive_ibc_denom(
                &channels.port_b.as_ref(),
                &channels.channel_id_b.as_ref(),
                &denom_a,
            )?;

            chain_driver_b.assert_eventual_wallet_amount(
                &user_b.address(),
                &denom_b.with_amount(send_amount + send_amount).as_ref(),
            )?;

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
