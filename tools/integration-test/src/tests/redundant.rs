use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::config::{self, Config, ModeConfig};
use ibc_relayer::link::RelayPath;

use ibc_relayer_types::events::IbcEvent;
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
        let denom_b = chains.node_b.denom();

        let relayer_a = chains.node_a.wallets().relayer().cloned();
        let relayer_b = chains.node_b.wallets().relayer().cloned();
        let wallet_a = chains.node_a.wallets().user1().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();

        let _balance_a = chains
            .node_a
            .chain_driver()
            .query_balance(&wallet_a.address(), &denom_a)?;

        let amount1 = denom_a.with_amount(1_u128);
        let amount2 = denom_b.with_amount(2_u128);

        let relay_path_b_to_a = RelayPath::new(channel.clone().flip().channel, false).unwrap();
        let relay_path_a_to_b = RelayPath::new(channel.channel, false).unwrap();

        let chain_driver_a = chains.node_a.chain_driver();
        let rpc_client_a = chain_driver_a.rpc_client().unwrap();
        let tx_config_a = chain_driver_a.tx_config();

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

        info!("[1] Building client update on B");

        let latest_height1 = chains.handle_a.query_application_status().unwrap().height;
        let update_height1 = latest_height1.increment();
        let mut msgs1 = chains
            .foreign_clients
            .client_a_to_b
            .wait_and_build_update_client(update_height1)
            .unwrap();

        info!("[1] Building Recv packet for B");

        let recv_msg1 = relay_path_a_to_b
            .build_recv_packet(&packet1, height1)
            .unwrap()
            .unwrap();

        msgs1.push(recv_msg1.clone());

        info!("[1] Sending Recv from A to B");

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

        dbg!(&events1);

        info!("[2] Building client update on A");

        let latest_height2 = chains.handle_b.query_application_status().unwrap().height;
        let update_height2 = latest_height2.increment();
        let mut msgs2 = chains
            .foreign_clients
            .client_b_to_a
            .wait_and_build_update_client(update_height2)
            .unwrap();

        info!("[2] Building Ack packet for A");

        let (height2, ack_event2) = events1
            .into_iter()
            .find_map(|event| match event.event {
                IbcEvent::WriteAcknowledgement(ev) => Some((event.height, ev)),
                _ => None,
            })
            .unwrap();

        dbg!(height2, &ack_event2);

        let write_ack_msg2 = relay_path_b_to_a
            .build_ack_from_recv_event(&ack_event2, height2)
            .unwrap()
            .unwrap();

        msgs2.push(write_ack_msg2.clone());

        info!("[2] Sending Ack from B to A");

        let events2 = chain_driver_a
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_a.value(),
                tx_config_a.value(),
                &relayer_a.as_ref().value().key,
                msgs2,
            ))
            .unwrap();

        dbg!(&events2);

        info!("[3] Initiating token transfer from B to A");

        let (height3, packet3) = chain_driver_b.ibc_transfer_token_with_height(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_a.address(),
            &amount2.as_ref(),
        )?;

        info!("[3] Building client update for B on A");

        let latest_height3 = chains.handle_b.query_application_status().unwrap().height;
        let update_height3 = latest_height3.increment();
        let mut msgs3 = chains
            .foreign_clients
            .client_b_to_a
            .wait_and_build_update_client(update_height3)
            .unwrap();

        info!("[3] Building Recv packet for A");

        let recv_msg3 = relay_path_b_to_a
            .build_recv_packet(&packet3, height3)
            .unwrap()
            .unwrap();

        msgs3.push(write_ack_msg2.clone());
        msgs3.push(recv_msg3.clone());

        info!("[3] Sending redundant Ack and non-redundant Recv packet from B to A");

        let events3 = chain_driver_a
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_a.value(),
                tx_config_a.value(),
                &relayer_a.as_ref().value().key,
                msgs3,
            ))
            .unwrap();

        dbg!(events3);

        Ok(())
    }
}
