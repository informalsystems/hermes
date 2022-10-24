use ibc_test_framework::{
    prelude::*,
    relayer::{
        channel::{assert_eventually_channel_established, init_channel},
        connection::{assert_eventually_connection_established, init_connection},
    },
};

#[test]
fn test_connection_handshake() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionHandshake)
}

#[test]
fn test_channel_handshake() -> Result<(), Error> {
    run_binary_connection_test(&ChannelHandshake)
}

pub struct ConnectionHandshake;

impl TestOverrides for ConnectionHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = false;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = true;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for ConnectionHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let (connection_id_b, _) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.foreign_clients.client_id_a(),
            &chains.foreign_clients.client_id_b(),
        )?;

        relayer.with_supervisor(|| {
            assert_eventually_connection_established(
                &chains.handle_b,
                &chains.handle_a,
                &connection_id_b.as_ref(),
            )?;

            Ok(())
        })
    }
}

pub struct ChannelHandshake;

impl TestOverrides for ChannelHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryConnectionTest for ChannelHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        let (channel_id_b, _) = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection.connection_id_a.as_ref(),
            &connection.connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        relayer.with_supervisor(|| {
            assert_eventually_channel_established(
                &chains.handle_b,
                &chains.handle_a,
                &channel_id_b.as_ref(),
                &port_b.as_ref(),
            )?;

            Ok(())
        })
    }
}
