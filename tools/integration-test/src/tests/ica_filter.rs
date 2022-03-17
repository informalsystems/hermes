use std::str::FromStr;

use ibc::core::ics04_channel::channel::State;
use ibc_relayer::config::{
    default::connection_delay as default_connection_delay,
    filter::{ChannelFilters, FilterPattern},
    PacketFilter,
};

use ibc_test_framework::{
    bootstrap::binary::connection::bootstrap_connection,
    prelude::*,
    relayer::channel::{assert_eventually_channel_established, query_channel_end},
};

#[test]
fn test_ica_filter_allow() -> Result<(), Error> {
    run_binary_chain_test(&IcaFilterTestAllow)
}

pub struct IcaFilterTestAllow;

impl TestOverrides for IcaFilterTestAllow {
    // Use deterministic identifiers for clients, connections, and channels
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.chain_command_path = "icad".to_string();
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        for chain in &mut config.chains {
            chain.packet_filter = PacketFilter::Allow(ChannelFilters::new(vec![(
                FilterPattern::Wildcard("ica*".parse().unwrap()),
                FilterPattern::Wildcard("*".parse().unwrap()),
            )]));
        }
    }
}

impl BinaryChainTest for IcaFilterTestAllow {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let connection =
            bootstrap_connection(&chains.foreign_clients, default_connection_delay(), false)?;
        dbg!(&connection);

        let wallet_a = chains.node_a.wallets().user1().cloned();
        dbg!(&wallet_a);

        let _handle = relayer.spawn_supervisor()?;

        chains.node_a.chain_driver().register_interchain_account(
            &wallet_a.address(),
            &connection.connection_id_a.as_ref(),
        )?;

        let channel_id_a: TaggedChannelId<ChainA, ChainB> =
            TaggedChannelId::new("channel-0".parse().unwrap());

        let icacontroller =
            PortId::from_str(&format!("icacontroller-{}", wallet_a.address().value())).unwrap();

        let port_id_a: TaggedPortIdRef<ChainA, ChainB> = DualTagged::new(&icacontroller);

        let counterparty_channel_id = assert_eventually_channel_established(
            chains.handle_a(),
            chains.handle_b(),
            &channel_id_a.as_ref(),
            &port_id_a,
        )?;

        dbg!(counterparty_channel_id);

        let ica_address = chains
            .node_a
            .chain_driver()
            .query_interchain_account(&wallet_a.address(), &connection.connection_id_a.as_ref())?;

        dbg!(ica_address);

        Ok(())
    }
}

#[test]
fn test_ica_filter_deny() -> Result<(), Error> {
    run_binary_chain_test(&IcaFilterTestDeny)
}

pub struct IcaFilterTestDeny;

impl TestOverrides for IcaFilterTestDeny {
    // Use deterministic identifiers for clients, connections, and channels
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.chain_command_path = "icad".to_string();
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;

        for chain in &mut config.chains {
            chain.packet_filter = PacketFilter::Deny(ChannelFilters::new(vec![(
                FilterPattern::Wildcard("ica*".parse().unwrap()),
                FilterPattern::Wildcard("*".parse().unwrap()),
            )]));
        }
    }
}

impl BinaryChainTest for IcaFilterTestDeny {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let connection =
            bootstrap_connection(&chains.foreign_clients, default_connection_delay(), false)?;

        let wallet_a = chains.node_a.wallets().user1().cloned();

        let _handle = relayer.spawn_supervisor()?;

        chains.node_a.chain_driver().register_interchain_account(
            &wallet_a.address(),
            &connection.connection_id_a.as_ref(),
        )?;

        std::thread::sleep(Duration::from_secs(30));

        let channel_id_a: TaggedChannelId<ChainA, ChainB> =
            TaggedChannelId::new("channel-0".parse().unwrap());

        let icacontroller =
            PortId::from_str(&format!("icacontroller-{}", wallet_a.address().value())).unwrap();

        let port_id_a: TaggedPortIdRef<ChainA, ChainB> = DualTagged::new(&icacontroller);

        let channel_end = query_channel_end(chains.handle_a(), &channel_id_a.as_ref(), &port_id_a)?;

        assert_eq(
            "channel end should still be in state Init",
            channel_end.value().state(),
            &State::Init,
        )
    }
}
