use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::config::{self, Config, ModeConfig};
use ibc_relayer::link::RelayPath;

use ibc_test_framework::prelude::*;

#[test]
fn test_redundant() -> Result<(), Error> {
    run_binary_channel_test(&RedundantTest {
        tx_confirmation: true,
    })
}

struct RedundantTest {
    tx_confirmation: bool,
}

impl TestOverrides for RedundantTest {
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
                clear_on_start: false,
                ..Default::default()
            },
        };
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for RedundantTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_a = chains.node_a.denom();

        let relayer_b = chains.node_b.wallets().relayer().cloned();
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let _balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let amount1 = denom_a.with_amount(1_u128);
        let amount2 = denom_a.with_amount(2_u128);

        let relay_path_a_to_b = RelayPath::new(channel.channel, false).unwrap();

        let chain_driver_a = chains.node_a.chain_driver();
        let chain_driver_b = chains.node_b.chain_driver();
        let rpc_client_b = chain_driver_b.rpc_client().unwrap();
        let tx_config_b = chain_driver_b.tx_config();

        info!("[1] Initiating token transfer from A to B");

        let (height1, packet1) = chain_driver_a.ibc_transfer_token_with_height(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &amount1.as_ref(),
        )?;

        dbg!(height1, &packet1);

        info!("[1] Building Recv packet");

        let recv_msg1 = relay_path_a_to_b
            .build_recv_packet(&packet1, height1)
            .unwrap()
            .unwrap();

        info!("[2] Initiating token transfer from A to B");

        let (height2, packet2) = chain_driver_a.ibc_transfer_token_with_height(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &amount2.as_ref(),
        )?;

        dbg!(height2, &packet2);

        info!("[2] Building Recv packet");

        let recv_msg2 = relay_path_a_to_b
            .build_recv_packet(&packet2, height2)
            .unwrap()
            .unwrap();

        let latest_height1 = chains.handle_a.query_application_status().unwrap().height;
        let update_height1 = latest_height1.increment();
        let mut msgs1 = chains
            .foreign_clients
            .client_a_to_b
            .wait_and_build_update_client(update_height1)
            .unwrap();

        msgs1.push(recv_msg1.clone());

        info!("[1] Sending packet from A to B");

        let events1 = chain_driver_b
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_b.value(),
                tx_config_b.value(),
                &relayer_b.as_ref().value().key,
                msgs1,
            ))
            .unwrap();

        dbg!(events1);

        let latest_height2 = chains.handle_a.query_application_status().unwrap().height;
        let update_height2 = latest_height2.increment();
        let mut msgs2 = chains
            .foreign_clients
            .client_a_to_b
            .wait_and_build_update_client(update_height2)
            .unwrap();

        msgs2.push(recv_msg1.clone());
        msgs2.push(recv_msg2.clone());

        info!("[2] Sending packets from A to B");

        let events2 = chain_driver_b
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_b.value(),
                tx_config_b.value(),
                &relayer_b.as_ref().value().key,
                msgs2,
            ))
            .unwrap();

        dbg!(events2);

        Ok(())
    }
}
