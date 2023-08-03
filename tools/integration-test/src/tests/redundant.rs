use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::config::{self, Config, ModeConfig};
use ibc_relayer::link::RelayPath;

use ibc_relayer_types::events::IbcEvent;
use ibc_test_framework::chain::config::set_voting_period;
use ibc_test_framework::prelude::*;

#[test]
#[cfg(not(feature = "interchain-security"))]
#[tracing::instrument]
fn test_redundant_recv() -> Result<(), Error> {
    run_binary_channel_test(&RedundantRecv { ics: false })
}

#[test]
#[cfg(feature = "interchain-security")]
#[tracing::instrument]
fn test_redundant_recv_ics() -> Result<(), Error> {
    use ibc_test_framework::framework::binary::channel::run_binary_interchain_security_channel_test;
    run_binary_interchain_security_channel_test(&RedundantRecv { ics: true })
}

#[test]
#[cfg(not(feature = "interchain-security"))]
#[tracing::instrument]
fn test_redundant_acks() -> Result<(), Error> {
    run_binary_channel_test(&RedundantAcksTest { ics: false })
}

#[test]
#[cfg(feature = "interchain-security")]
#[tracing::instrument]
fn test_redundant_acks_ics() -> Result<(), Error> {
    use ibc_test_framework::framework::binary::channel::run_binary_interchain_security_channel_test;
    run_binary_interchain_security_channel_test(&RedundantAcksTest { ics: true })
}

struct RedundantRecv {
    ics: bool,
}

impl TestOverrides for RedundantRecv {
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

        if self.ics {
            for chain_config in config.chains.iter_mut() {
                if chain_config.id == ChainId::from_string("ibcconsumer") {
                    chain_config.ccv_consumer_chain = true;
                    chain_config.trusting_period = Some(Duration::from_secs(99));
                }
            }
        }
    }

    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        if self.ics {
            // Consumer chain doesn't have a gov key.
            if genesis
                .get_mut("app_state")
                .and_then(|app_state| app_state.get("gov"))
                .is_some()
            {
                set_voting_period(genesis, "10s")?;
            }
        }

        Ok(())
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for RedundantRecv {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let denom_b = chains.node_b.denom();

        let relayer_a = chains.node_a.wallets().relayer().cloned();
        let wallet_b = chains.node_b.wallets().user1().cloned();
        let wallet_a = chains.node_a.wallets().user1().cloned();

        let amount1 = denom_b.with_amount(1_u128);
        let amount2 = denom_b.with_amount(2_u128);

        let relay_path_b_to_a = RelayPath::new(channel.clone().flip().channel, false).unwrap();

        let chain_driver_b = chains.node_b.chain_driver();
        let chain_driver_a = chains.node_a.chain_driver();
        let rpc_client_a = chain_driver_a.rpc_client().unwrap();
        let tx_config_a = chain_driver_a.tx_config();

        info!("[1] Initiating token transfer from B to A");

        let (height1, packet1) = chain_driver_b.ibc_transfer_token_with_height(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_a.address(),
            &amount1.as_ref(),
        )?;

        info!("[1] Building client update");

        let latest_height1 = chains.handle_b.query_application_status().unwrap().height;
        let update_height1 = latest_height1.increment();
        let mut msgs1 = chains
            .foreign_clients
            .client_b_to_a
            .wait_and_build_update_client(update_height1)
            .unwrap();

        info!("[1] Building Recv packet");

        let recv_msg1 = relay_path_b_to_a
            .build_recv_packet(&packet1, height1)
            .unwrap()
            .unwrap();

        msgs1.push(recv_msg1.clone());

        info!("[1] Sending Recv from B to A");

        let events1 = chain_driver_a
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_a.value(),
                tx_config_a.value(),
                &relayer_a.as_ref().value().key,
                msgs1,
            ))
            .unwrap();

        info!("[1] Events emitted in response to Recv: {events1:#?}");

        info!("[2] Initiating token transfer from B to A");

        let (height2, packet2) = chain_driver_b.ibc_transfer_token_with_height(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_a.address(),
            &amount2.as_ref(),
        )?;

        info!("[2] Building client update");

        let latest_height2 = chains.handle_b.query_application_status().unwrap().height;
        let update_height2 = latest_height2.increment();
        let mut msgs2 = chains
            .foreign_clients
            .client_b_to_a
            .wait_and_build_update_client(update_height2)
            .unwrap();

        info!("[2] Building Recv packet");

        let recv_msg2 = relay_path_b_to_a
            .build_recv_packet(&packet2, height2)
            .unwrap()
            .unwrap();

        msgs2.push(recv_msg1.clone());
        msgs2.push(recv_msg2.clone());

        info!("[2] Sending redundant and non-redundant Recv from B to A");

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

        info!("[2] Events emitted in response to redundant and non-redundant Recv: {events2:#?}");

        Ok(())
    }
}

struct RedundantAcksTest {
    ics: bool,
}

impl TestOverrides for RedundantAcksTest {
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

        if self.ics {
            for chain_config in config.chains.iter_mut() {
                if chain_config.id == ChainId::from_string("ibcconsumer") {
                    chain_config.ccv_consumer_chain = true;
                    chain_config.trusting_period = Some(Duration::from_secs(99));
                }
            }
        }
    }

    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        if self.ics {
            // Consumer chain doesn't have a gov key.
            if genesis
                .get_mut("app_state")
                .and_then(|app_state| app_state.get("gov"))
                .is_some()
            {
                set_voting_period(genesis, "10s")?;
            }
        }

        Ok(())
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for RedundantAcksTest {
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

        let amount1 = denom_b.with_amount(1_u128);
        let amount2 = denom_a.with_amount(2_u128);

        let relay_path_b_to_a = RelayPath::new(channel.clone().flip().channel, false).unwrap();
        let relay_path_a_to_b = RelayPath::new(channel.channel, false).unwrap();

        let chain_driver_a = chains.node_a.chain_driver();
        let rpc_client_a = chain_driver_a.rpc_client().unwrap();
        let tx_config_a = chain_driver_a.tx_config();

        let chain_driver_b = chains.node_b.chain_driver();
        let rpc_client_b = chain_driver_b.rpc_client().unwrap();
        let tx_config_b = chain_driver_b.tx_config();

        info!("[1] Initiating token transfer from B to A");

        let (height1, packet1) = chain_driver_b.ibc_transfer_token_with_height(
            &channel.port_b.as_ref(),
            &channel.channel_id_b.as_ref(),
            &wallet_b.as_ref(),
            &wallet_a.address(),
            &amount1.as_ref(),
        )?;

        info!("[1] Building client update on A");

        let latest_height1 = chains.handle_b.query_application_status().unwrap().height;
        let update_height1 = latest_height1.increment();
        let mut msgs1 = chains
            .foreign_clients
            .client_b_to_a
            .wait_and_build_update_client(update_height1)
            .unwrap();

        info!("[1] Building Recv packet for A");

        let recv_msg1 = relay_path_b_to_a
            .build_recv_packet(&packet1, height1)
            .unwrap()
            .unwrap();

        msgs1.push(recv_msg1.clone());

        info!("[1] Sending Recv from B to A");

        let events1 = chain_driver_a
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_a.value(),
                tx_config_a.value(),
                &relayer_a.as_ref().value().key,
                msgs1,
            ))
            .unwrap();

        debug!("[1] Events emitted in response to Recv: {events1:#?}");

        info!("[2] Building client update on B");

        let latest_height2 = chains.handle_a.query_application_status().unwrap().height;
        let update_height2 = latest_height2.increment();
        let mut msgs2 = chains
            .foreign_clients
            .client_a_to_b
            .wait_and_build_update_client(update_height2)
            .unwrap();

        info!("[2] Building Ack packet for B");

        let (height2, ack_event2) = events1
            .into_iter()
            .find_map(|event| match event.event {
                IbcEvent::WriteAcknowledgement(ev) => Some((event.height, ev)),
                _ => None,
            })
            .unwrap();

        let write_ack_msg2 = relay_path_a_to_b
            .build_ack_from_recv_event(&ack_event2, height2)
            .unwrap()
            .unwrap();

        msgs2.push(write_ack_msg2.clone());

        info!("[2] Sending Ack from A to B");

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

        info!("[2] Events emitted in response to Ack: {events2:#?}");

        info!("[3] Initiating token transfer from A to B");

        let (height3, packet3) = chain_driver_a.ibc_transfer_token_with_height(
            &channel.port_a.as_ref(),
            &channel.channel_id_a.as_ref(),
            &wallet_a.as_ref(),
            &wallet_b.address(),
            &amount2.as_ref(),
        )?;

        info!("[3] Building client update for A on B");

        let latest_height3 = chains.handle_a.query_application_status().unwrap().height;
        let update_height3 = latest_height3.increment();
        let mut msgs3 = chains
            .foreign_clients
            .client_a_to_b
            .wait_and_build_update_client(update_height3)
            .unwrap();

        info!("[3] Building Recv packet for B");

        let recv_msg3 = relay_path_a_to_b
            .build_recv_packet(&packet3, height3)
            .unwrap()
            .unwrap();

        msgs3.push(write_ack_msg2.clone());
        msgs3.push(recv_msg3.clone());

        info!("[3] Sending redundant Ack and non-redundant Recv packet from A to B");

        let events3 = chain_driver_b
            .value()
            .runtime
            .block_on(simple_send_tx(
                rpc_client_b.value(),
                tx_config_b.value(),
                &relayer_b.as_ref().value().key,
                msgs3,
            ))
            .unwrap();

        info!(
            "[3] Events emitted in response to redundant Ack and non-redundant Recv: {events3:#?}"
        );

        Ok(())
    }
}
