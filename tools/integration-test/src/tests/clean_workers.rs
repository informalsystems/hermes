use ibc_relayer::config::{self, ModeConfig};
use ibc_relayer::object::ObjectType;
use ibc_test_framework::{prelude::*, util::random::random_u128_range};

#[test]
fn test_clean_workers() -> Result<(), Error> {
    run_binary_channel_test(&CleanWorkersTest)
}

pub struct CleanWorkersTest;

impl TestOverrides for CleanWorkersTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            clients: config::Clients {
                enabled: false,
                refresh: false,
                misbehaviour: false,
            },
            connections: config::Connections { enabled: false },
            channels: config::Channels { enabled: false },
            packets: config::Packets {
                enabled: true,
                clear_interval: 10,
                clear_on_start: false,
                tx_confirmation: false,
                ..Default::default()
            },
        };
    }
}

impl BinaryChannelTest for CleanWorkersTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let amount1 = random_u128_range(1000, 5000);

        let supervisor = relayer.spawn_supervisor()?;

        // Transfer tokens so that the packet workers are spawned
        chains.node_a.chain_driver().ibc_transfer_token(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &denom_a.with_amount(amount1).as_ref(),
        )?;

        // Assert the packet workers are correctly spawned
        assert_eventual_packet_workers(&supervisor, 2)?;

        // Assert that idle packet workers are eventually removed
        assert_eventual_packet_workers(&supervisor, 0)?;

        Ok(())
    }
}

fn assert_eventual_packet_workers(supervisor: &SupervisorHandle, goal: usize) -> Result<(), Error> {
    assert_eventually_succeed(
        "eventual packet workers",
        50,
        Duration::from_secs(10),
        || {
            let state = supervisor.dump_state()?;

            let packet_workers_amount =
                if let Some(packet_workers) = state.workers.get(&ObjectType::Packet) {
                    packet_workers.len()
                } else {
                    0
                };
            if packet_workers_amount == goal {
                return Ok(());
            }
            Err(Error::generic(eyre!(
                "current number of workers `{packet_workers_amount}` does not match goal `{goal}`"
            )))
        },
    )?;

    Ok(())
}
