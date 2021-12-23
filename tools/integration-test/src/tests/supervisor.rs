use core::time::Duration;
use ibc::core::ics03_connection::connection::State as ConnectionState;
use ibc::core::ics04_channel::channel::State as ChannelState;
use ibc_relayer::config::{self, Config, ModeConfig};

use crate::prelude::*;
pub use crate::relayer::channel::{init_channel, query_channel_end};
pub use crate::relayer::connection::{init_connection, query_connection_end};

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
        let connection_id_b = init_connection(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_b_to_a.tagged_client_id(),
            &chains.client_a_to_b.tagged_client_id(),
        )?;

        let connection_id_a = assert_eventually_succeed(
            "connection should eventually open",
            20,
            Duration::from_secs(1),
            || {
                let connection_end_b =
                    query_connection_end(&chains.handle_b, &connection_id_b.as_ref())?;

                if !connection_end_b
                    .value()
                    .state_matches(&ConnectionState::Open)
                {
                    return Err(Error::generic(eyre!(
                        "expected connection end B to be in open state"
                    )));
                }

                let connection_id_a = connection_end_b
                    .tagged_counterparty_connection_id()
                    .ok_or_else(|| {
                        eyre!("expected counterparty connection id to present on open connection")
                    })?;

                let connection_end_a =
                    query_connection_end(&chains.handle_a, &connection_id_a.as_ref())?;

                if !connection_end_a
                    .value()
                    .state_matches(&ConnectionState::Open)
                {
                    return Err(Error::generic(eyre!(
                        "expected connection end A to be in open state"
                    )));
                }

                Ok(connection_id_a)
            },
        )?;

        let port_a = tagged_transfer_port();
        let port_b = tagged_transfer_port();

        info!("performing init channel");

        let channel_id_b = init_channel(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection_id_a.as_ref(),
            &connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
        )?;

        assert_eventually_succeed(
            "channel should eventually open",
            20,
            Duration::from_secs(1),
            || {
                let channel_end_b =
                    query_channel_end(&chains.handle_b, &channel_id_b.as_ref(), &port_b.as_ref())?;

                let state_b = channel_end_b.value().state();
                info!("channel b state: {:?}", state_b);

                if !channel_end_b.value().state_matches(&ChannelState::Open) {
                    return Err(Error::generic(eyre!(
                        "expected channel end A to be in open state"
                    )));
                }

                let channel_id_a =
                    channel_end_b
                        .tagged_counterparty_channel_id()
                        .ok_or_else(|| {
                            eyre!("expected counterparty channel id to present on open channel")
                        })?;

                let channel_end_a =
                    query_channel_end(&chains.handle_a, &channel_id_a.as_ref(), &port_a.as_ref())?;

                if !channel_end_a.value().state_matches(&ChannelState::Open) {
                    return Err(Error::generic(eyre!(
                        "expected channel end B to be in open state"
                    )));
                }

                Ok(channel_id_a)
            },
        )?;

        Ok(())
    }
}
