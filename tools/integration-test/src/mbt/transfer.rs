use ibc_relayer::config::{
    Channels as ConfigChannels, Clients as ConfigClients, Connections as ConfigConnections,
    ModeConfig, Packets as ConfigPackets,
};
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle, SupervisorOptions};

use crate::framework::binary::chain::run_self_connected_binary_chain_test;
use crate::prelude::*;
use crate::types::tagged::mono::Tagged;

use super::state::Action;

use super::utils::{get_chain, parse_itf_from_json, CLIENT_EXPIRY};

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    run_binary_chain_test(&IbcTransferMBT)
}

/**
   Test that IBC token transfer can still work with a single
   chain that is connected to itself.
*/
#[test]
fn test_self_connected_ibc_transfer() -> Result<(), Error> {
    run_self_connected_binary_chain_test(&IbcTransferMBT)
}

pub struct IbcTransferMBT;

impl TestOverrides for IbcTransferMBT {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.bootstrap_with_random_ids = false;
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode = ModeConfig {
            clients: ConfigClients {
                enabled: true,
                refresh: true,
                misbehaviour: true,
            },
            connections: ConfigConnections { enabled: true },
            channels: ConfigChannels { enabled: true },
            packets: ConfigPackets {
                enabled: true,
                clear_interval: 10,
                clear_on_start: true,
                tx_confirmation: true,
            },
        };

        for mut chain_config in config.chains.iter_mut() {
            chain_config.trusting_period = Some(CLIENT_EXPIRY);
        }
    }

    fn spawn_supervisor(
        &self,
        _config: &SharedConfig,
        _registry: &SharedRegistry<impl ChainHandle>,
    ) -> Result<Option<SupervisorHandle>, Error> {
        Ok(None)
    }
}

impl BinaryChainTest for IbcTransferMBT {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let itf_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/spec/example/counterexample.itf.json"
        );

        let mut channels_a_b = None;
        let mut refresh_task_a = None;
        let mut refresh_task_b = None;
        // no connections and channel is created at this point

        // relayer is spawned
        let _supervisor = spawn_supervisor(
            chains.config.clone(),
            chains.registry.clone(),
            None,
            SupervisorOptions {
                health_check: false,
                force_full_scan: false,
            },
        )?;

        for state in parse_itf_from_json(itf_path) {
            match state.action {
                Action::Null => {
                    info!("[Init] Setting up chains");
                    super::handlers::setup_chains(&chains)?;
                    info!("[Init] Done");
                }
                Action::LocalTransfer {
                    chain_id,
                    source,
                    target,
                    denom,
                    amount,
                } => {
                    info!("[LocalTransfer] Init");
                    let node: Tagged<ChainA, _> = get_chain(&chains, chain_id);
                    super::handlers::local_transfer_handler(node, source, target, denom, amount)?;
                    info!("[LocalTransfer] Done");
                }
                Action::CreateChannel { chains: chain_pair } => {
                    assert_eq!(chain_pair.0.len(), 2);
                    assert!(chain_pair.0.contains(&1));
                    assert!(chain_pair.0.contains(&2));
                    info!("[CreateChannel] between {:?}", chain_pair.0);

                    super::handlers::create_channel(
                        &chains.handle_a,
                        &chains.handle_b,
                        &mut channels_a_b,
                        &mut refresh_task_a,
                        &mut refresh_task_b,
                    )?;

                    info!("[CreateChannel] Done");
                }
                Action::ExpireChannel { chains: chain_pair } => {
                    assert_eq!(chain_pair.0.len(), 2);
                    assert!(chain_pair.0.contains(&1));
                    assert!(chain_pair.0.contains(&2));
                    info!("[ExpireChannel] between {:?}", chain_pair.0);

                    super::handlers::expire_channel(
                        &mut channels_a_b,
                        &mut refresh_task_a,
                        &mut refresh_task_b,
                    )?;
                    info!("[ExpireChannel] Done");
                }
                Action::IBCTransferSendPacket { packet } => {
                    info!("[IBCTransferSendPacket] {:?}", packet);

                    match (
                        packet.channel.source.chain_id,
                        packet.channel.target.chain_id,
                    ) {
                        (1, 2) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_a,
                                    channels_a_b.as_ref().expect("one channel")
                                )?
                                .is_empty(),
                                "no packets present"
                            );

                            super::handlers::ibc_transfer_send_packet(
                                chains.node_a.as_ref(),
                                chains.node_b.as_ref(),
                                &channels_a_b,
                                &packet,
                            )?;

                            assert_eq!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_a,
                                    channels_a_b.as_ref().expect("one channel")
                                )?
                                .len(),
                                1,
                                "one packet is sent"
                            );
                        }
                        (2, 1) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_b,
                                    &channels_a_b.as_ref().expect("one channel").clone().flip()
                                )?
                                .is_empty(),
                                "no packets present"
                            );

                            super::handlers::ibc_transfer_send_packet(
                                chains.node_b.as_ref(),
                                chains.node_a.as_ref(),
                                &channels_a_b.clone().map(|x| x.flip()),
                                &packet,
                            )?;
                            assert_eq!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_b,
                                    &channels_a_b.as_ref().expect("one channel").clone().flip()
                                )?
                                .len(),
                                1,
                                "one packet is present"
                            );
                        }
                        _ => unreachable!(),
                    }

                    info!("[IBCTransferSendPacket] Done");
                }
                Action::IBCTransferReceivePacket { packet } => {
                    info!("[IBCTransferReceivePacket] {:?}", packet);
                    match (
                        packet.channel.source.chain_id,
                        packet.channel.target.chain_id,
                    ) {
                        (1, 2) => {
                            super::handlers::ibc_transfer_receive_packet(
                                chains.node_a.as_ref(),
                                chains.node_b.as_ref(),
                                &channels_a_b,
                                &packet,
                            )?;
                            assert_eq!(
                                super::utils::get_acknowledged_packets_at_dst(
                                    &chains.handle_b,
                                    &channels_a_b.as_ref().expect("one channel").clone().flip()
                                )?
                                .len(),
                                1,
                                "one packet is received and sent acknowledgement"
                            );
                        }
                        (2, 1) => {
                            super::handlers::ibc_transfer_receive_packet(
                                chains.node_b.as_ref(),
                                chains.node_a.as_ref(),
                                &channels_a_b.clone().map(|x| x.flip()),
                                &packet,
                            )?;
                            assert_eq!(
                                super::utils::get_acknowledged_packets_at_dst(
                                    &chains.handle_a,
                                    channels_a_b.as_ref().expect("one channel")
                                )?
                                .len(),
                                1,
                                "one packet is received and sent acknowledgement"
                            );
                        }
                        _ => unreachable!(),
                    }

                    info!("[IBCTransferReceivePacket] Done");
                }
                Action::IBCTransferAcknowledgePacket { packet } => {
                    info!("[IBCTransferAcknowledgePacket] {:?}", packet);
                    super::utils::wait_for_client();
                    match (
                        packet.channel.source.chain_id,
                        packet.channel.target.chain_id,
                    ) {
                        (1, 2) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_a,
                                    channels_a_b.as_ref().expect("one channel")
                                )?
                                .is_empty(),
                                "commitment is completed"
                            );
                        }
                        (2, 1) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_b,
                                    &channels_a_b.as_ref().expect("one channel").clone().flip()
                                )?
                                .is_empty(),
                                "commitment is completed"
                            );
                        }
                        _ => unreachable!(),
                    }

                    info!("[IBCTransferAcknowledgePacket] Done");
                }
                Action::IBCTransferTimeoutPacket { packet } => {
                    info!("[IBCTransferTimeoutPacket] {:?}", packet);

                    match (
                        packet.channel.source.chain_id,
                        packet.channel.target.chain_id,
                    ) {
                        (1, 2) => {}
                        (2, 1) => {}
                        _ => unreachable!(),
                    }

                    info!("[IBCTransferTimeoutPacket] Done")
                }
            }
        }

        Ok(())
    }
}
