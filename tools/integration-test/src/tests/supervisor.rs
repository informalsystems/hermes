use ibc_relayer::config::{self, Config, ModeConfig};

use crate::prelude::*;
pub use crate::relayer::channel::{
    assert_eventually_channel_established, init_channel, query_channel_end,
};
pub use crate::relayer::connection::{
    assert_eventually_connection_established, init_connection, query_connection_end,
};

#[test]
fn test_supervisor() -> Result<(), Error> {
    run_binary_chain_test(&SupervisorTest)
}

struct SupervisorTest;

impl TestOverrides for SupervisorTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            clients: config::Clients {
                enabled: true,
                refresh: true,
                misbehaviour: true,
            },
            connections: config::Connections { enabled: true },
            channels: config::Channels { enabled: true },
            packets: config::Packets {
                enabled: true,
                clear_interval: 10,
                clear_on_start: true,
                filter: false,
                tx_confirmation: true,
            },
        };
    }
}

impl BinaryChainTest for SupervisorTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let (connection_id_b, _) = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_b_to_a.tagged_client_id(),
            &chains.client_a_to_b.tagged_client_id(),
        )?;

        let connection_id_a = assert_eventually_connection_established(
            &chains.handle_b,
            &chains.handle_a,
            &connection_id_b.as_ref(),
        )?;

        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        let (channel_id_b, _) = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection_id_a.as_ref(),
            &connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        assert_eventually_channel_established(
            &chains.handle_b,
            &chains.handle_a,
            &channel_id_b.as_ref(),
            &port_b.as_ref(),
        )?;

        Ok(())
    }
}
