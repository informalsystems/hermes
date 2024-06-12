use ibc_test_framework::{
    prelude::*,
    relayer::{
        channel::{
            ack_channel, assert_eventually_channel_established, init_channel,
            init_channel_optimistic, try_channel,
        },
        connection::{
            ack_connection, assert_eventually_connection_established, init_connection,
            try_connection,
        },
    },
};

#[test]
fn test_connection_open_handshake() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionOpenHandshake {
        enable_worker: true,
    })
}

#[test]
fn test_connection_open_handshake_no_worker() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionOpenHandshake {
        enable_worker: false,
    })
}

#[test]
fn test_connection_try_handshake() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionTryHandshake {
        enable_worker: true,
    })
}

#[test]
fn test_connection_try_handshake_no_worker() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionTryHandshake {
        enable_worker: false,
    })
}

#[test]
fn test_connection_ack_handshake() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionAckHandshake {
        enable_worker: true,
    })
}

#[test]
fn test_connection_ack_handshake_no_worker() -> Result<(), Error> {
    run_binary_chain_test(&ConnectionAckHandshake {
        enable_worker: false,
    })
}

#[test]
fn test_channel_open_handshake() -> Result<(), Error> {
    run_binary_connection_test(&ChannelOpenHandshake {
        enable_worker: true,
    })
}

#[test]
fn test_channel_open_handshake_no_worker() -> Result<(), Error> {
    run_binary_connection_test(&ChannelOpenHandshake {
        enable_worker: false,
    })
}

#[test]
fn test_channel_try_handshake() -> Result<(), Error> {
    run_binary_connection_test(&ChannelTryHandshake {
        enable_worker: true,
    })
}

#[test]
fn test_channel_try_handshake_no_worker() -> Result<(), Error> {
    run_binary_connection_test(&ChannelTryHandshake {
        enable_worker: false,
    })
}

#[test]
fn test_channel_ack_handshake() -> Result<(), Error> {
    run_binary_connection_test(&ChannelAckHandshake {
        enable_worker: true,
    })
}

#[test]
fn test_channel_ack_handshake_no_worker() -> Result<(), Error> {
    run_binary_connection_test(&ChannelAckHandshake {
        enable_worker: false,
    })
}

#[test]
fn test_channel_optimistic_handshake() -> Result<(), Error> {
    run_binary_chain_test(&OptimisticChannelOpenHandshake {})
}

pub struct ConnectionOpenHandshake {
    enable_worker: bool,
}

impl TestOverrides for ConnectionOpenHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.connections.enabled = self.enable_worker;

        config.mode.channels.enabled = false;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for ConnectionOpenHandshake {
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
            let result = assert_eventually_connection_established(
                &chains.handle_b,
                &chains.handle_a,
                &connection_id_b.as_ref(),
            );

            if self.enable_worker {
                result?;
            } else {
                assert_err(
                    "connection should not end up open when worker is disabled",
                    result,
                )?;
            }

            Ok(())
        })
    }
}

pub struct ConnectionTryHandshake {
    enable_worker: bool,
}

impl TestOverrides for ConnectionTryHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.connections.enabled = self.enable_worker;

        config.mode.channels.enabled = false;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for ConnectionTryHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let (_connection_id_on_b, connection_to_a_on_b) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.foreign_clients.client_id_a(),
            &chains.foreign_clients.client_id_b(),
        )?;

        let (connection_id_on_a, _connection_to_b_on_a) =
            try_connection(&chains.handle_b, &chains.handle_a, &connection_to_a_on_b)?;

        relayer.with_supervisor(|| {
            let result = assert_eventually_connection_established(
                &chains.handle_a,
                &chains.handle_b,
                &connection_id_on_a.as_ref(),
            );

            if self.enable_worker {
                result?;
            } else {
                assert_err(
                    "connection should not end up open when worker is disabled",
                    result,
                )?;
            }

            Ok(())
        })
    }
}

pub struct ConnectionAckHandshake {
    enable_worker: bool,
}

impl TestOverrides for ConnectionAckHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.connections.enabled = self.enable_worker;

        config.mode.channels.enabled = false;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for ConnectionAckHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let (connection_id_on_b, connection_to_a_on_b) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.foreign_clients.client_id_a(),
            &chains.foreign_clients.client_id_b(),
        )?;

        let (_connection_id_on_a, connection_to_b_on_a) =
            try_connection(&chains.handle_b, &chains.handle_a, &connection_to_a_on_b)?;

        let _ = ack_connection(&chains.handle_a, &chains.handle_b, &connection_to_b_on_a)?;

        relayer.with_supervisor(|| {
            let result = assert_eventually_connection_established(
                &chains.handle_b,
                &chains.handle_a,
                &connection_id_on_b.as_ref(),
            );

            if self.enable_worker {
                result?;
            } else {
                assert_err(
                    "connection should not end up open when worker is disabled",
                    result,
                )?;
            }

            Ok(())
        })
    }
}

pub struct ChannelOpenHandshake {
    enable_worker: bool,
}

impl TestOverrides for ChannelOpenHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = self.enable_worker;

        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryConnectionTest for ChannelOpenHandshake {
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
            let result = assert_eventually_channel_established(
                &chains.handle_b,
                &chains.handle_a,
                &channel_id_b.as_ref(),
                &port_b.as_ref(),
            );

            if self.enable_worker {
                result?;
            } else {
                assert_err(
                    "channel should not end up open when worker is disabled",
                    result,
                )?;
            }

            Ok(())
        })
    }
}

pub struct ChannelTryHandshake {
    enable_worker: bool,
}

impl TestOverrides for ChannelTryHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = self.enable_worker;

        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryConnectionTest for ChannelTryHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        let (_channel_id_on_b, channel_to_a_on_b) = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection.connection_id_a.as_ref(),
            &connection.connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        let (channel_id_on_a, _channel_to_b_on_a) =
            try_channel(&chains.handle_a, &chains.handle_b, &channel_to_a_on_b)?;

        relayer.with_supervisor(|| {
            let result = assert_eventually_channel_established(
                &chains.handle_a,
                &chains.handle_b,
                &channel_id_on_a.as_ref(),
                &port_a.as_ref(),
            );

            if self.enable_worker {
                result?;
            } else {
                assert_err(
                    "channel should not end up open when worker is disabled",
                    result,
                )?;
            }

            Ok(())
        })
    }
}

pub struct ChannelAckHandshake {
    enable_worker: bool,
}

impl TestOverrides for ChannelAckHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = self.enable_worker;

        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
        config.mode.connections.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryConnectionTest for ChannelAckHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        let (channel_id_on_b, channel_to_a_on_b) = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection.connection_id_a.as_ref(),
            &connection.connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        let (_channel_id_on_a, channel_to_b_on_a) =
            try_channel(&chains.handle_a, &chains.handle_b, &channel_to_a_on_b)?;

        let _ = ack_channel(&chains.handle_b, &chains.handle_a, &channel_to_b_on_a)?;

        relayer.with_supervisor(|| {
            let result = assert_eventually_channel_established(
                &chains.handle_b,
                &chains.handle_a,
                &channel_id_on_b.as_ref(),
                &port_b.as_ref(),
            );

            if self.enable_worker {
                result?;
            } else {
                assert_err(
                    "channel should not end up open when worker is disabled",
                    result,
                )?;
            }

            Ok(())
        })
    }
}

pub struct OptimisticChannelOpenHandshake {}

impl TestOverrides for OptimisticChannelOpenHandshake {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.connections.enabled = true;
        config.mode.channels.enabled = true;
        config.mode.packets.enabled = false;
        config.mode.clients.enabled = false;
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChainTest for OptimisticChannelOpenHandshake {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        // Send conn-open-init to B
        let (connection_id_b, _) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.foreign_clients.client_id_a(),
            &chains.foreign_clients.client_id_b(),
        )?;

        // Optimistically send chan-open-init to B, without a connection available yet on A
        let channel_id_b = init_channel_optimistic(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        // The channel should eventually be in OPEN state
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
