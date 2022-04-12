use ibc_relayer::config::{
    Channels as ConfigChannels, Clients as ConfigClients, Connections as ConfigConnections,
    ModeConfig, Packets as ConfigPackets,
};

use ibc_test_framework::prelude::*;
use ibc_test_framework::types::tagged::mono::Tagged;

use super::state::{Action, State};

use super::utils::{get_chain, parse_itf_from_json, CLIENT_EXPIRY};

const TEST_NAMES: &[&str] = &[
    "LocalTransferInv",
    "IBCTransferAcknowledgePacketInv",
    "IBCTransferTimeoutPacketInv",
];
const NUM_TRACES_PER_TEST: usize = 2;
const APALACHE_EXEC: &str = "apalache-mc";

fn generate_mbt_traces(
    apalache_path: &str,
    test_name: &str,
    num_traces: usize,
) -> Result<Vec<Vec<State>>, Error> {
    let temp_dir = tempfile::TempDir::new()?;
    let run_dir = temp_dir.path().join("run");
    let tla_path = concat!(env!("CARGO_MANIFEST_DIR"), "/spec/MC_Transfer.tla");
    let mut cmd = std::process::Command::new(apalache_path);
    cmd.arg("check")
        .arg("--init=Init")
        .arg("--next=Next")
        .arg(&format!("--inv={test_name}"))
        .arg(&format!("--max-error={num_traces}"))
        .arg(&format!(
            "--run-dir={}",
            run_dir.to_str().expect("no panic")
        ))
        .arg(&format!(
            "--out-dir={}",
            temp_dir.path().to_str().expect("no panic")
        ))
        .arg(tla_path);
    let _ = cmd.status().expect("failed to execute process");

    Ok(std::fs::read_dir(run_dir)?
        .flatten()
        .map(|entry| entry.path())
        .filter(|file_path| file_path.is_file())
        .flat_map(|file_path| {
            file_path
                .file_name()
                .and_then(|file_name| file_name.to_str())
                .and_then(|file_name| {
                    (file_name != "counterexample.itf.json"
                        && file_name.starts_with("counterexample")
                        && file_name.ends_with(".itf.json"))
                    .then(|| parse_itf_from_json(file_path.to_str().expect("should not panic")))
                })
        })
        .collect())
}

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    for test_name in TEST_NAMES {
        for trace in generate_mbt_traces(APALACHE_EXEC, test_name, NUM_TRACES_PER_TEST)? {
            run_binary_channel_test(&IbcTransferMBT(trace))?;
        }
    }
    Ok(())
}

/**
   Test that IBC token transfer can still work with a single
   chain that is connected to itself.
*/
#[test]
#[cfg(feature = "manual")]
fn test_self_connected_ibc_transfer() -> Result<(), Error> {
    use ibc_test_framework::framework::binary::chain::run_self_connected_binary_chain_test;
    use ibc_test_framework::framework::binary::channel::RunBinaryChannelTest;

    for test_name in TEST_NAMES {
        for trace in generate_mbt_traces(APALACHE_EXEC, test_name, NUM_TRACES_PER_TEST)? {
            run_self_connected_binary_chain_test(&RunBinaryConnectionTest::new(
                &RunBinaryChannelTest::new(&IbcTransferMBT(trace)),
            ))?;
        }
    }
    Ok(())
}

pub struct IbcTransferMBT(Vec<State>);

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

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl BinaryChannelTest for IbcTransferMBT {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        channels: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        // relayer is spawned
        let mut supervisor = Some(relayer.spawn_supervisor()?);

        for state in &self.0 {
            match &state.action {
                Action::Null => {
                    info!("[Init] Setting up chains");
                    // super::handlers::setup_chains(&chains)?;
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
                    let node: Tagged<ChainA, _> = get_chain(&chains, *chain_id);
                    super::handlers::local_transfer_handler(
                        node, *source, *target, *denom, *amount,
                    )?;
                    info!("[LocalTransfer] Done");
                }
                Action::RestoreRelay => {
                    // assert_eq!(chain_pair.0.len(), 2);
                    // assert!(chain_pair.0.contains(&1));
                    // assert!(chain_pair.0.contains(&2));
                    // info!("[CreateChannel] between {:?}", chain_pair.0);

                    // // super::handlers::create_channel(
                    // //     &chains.handle_a,
                    // //     &chains.handle_b,
                    // //     &mut channels_a_b,
                    // //     &mut refresh_task_a,
                    // //     &mut refresh_task_b,
                    // // )?;

                    if supervisor.is_none() {
                        supervisor = Some(relayer.spawn_supervisor()?);
                    }

                    info!("[RestoreRelay] Done");
                }
                Action::InterruptRelay => {
                    // assert_eq!(chain_pair.0.len(), 2);
                    // assert!(chain_pair.0.contains(&1));
                    // assert!(chain_pair.0.contains(&2));
                    // info!("[ExpireChannel] between {:?}", chain_pair.0);

                    // // super::handlers::expire_channel(
                    // //     &mut channels_a_b,
                    // //     &mut refresh_task_a,
                    // //     &mut refresh_task_b,
                    // // )?;
                    supervisor.take().expect("one").shutdown();

                    info!("[InterruptRelay] Done");
                }
                Action::IBCTransferSendPacket { packet } => {
                    info!("[IBCTransferSendPacket] {:?}", packet);

                    match (packet.source_chain_id, packet.target_chain_id) {
                        (1, 2) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_a,
                                    &channels
                                )?
                                .is_empty(),
                                "no packets present"
                            );

                            super::handlers::ibc_transfer_send_packet(
                                chains.node_a.as_ref(),
                                chains.node_b.as_ref(),
                                &channels,
                                packet,
                            )?;

                            assert_eq!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_a,
                                    &channels,
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
                                    &channels.clone().flip()
                                )?
                                .is_empty(),
                                "no packets present"
                            );

                            super::handlers::ibc_transfer_send_packet(
                                chains.node_b.as_ref(),
                                chains.node_a.as_ref(),
                                &channels.clone().flip(),
                                packet,
                            )?;

                            assert_eq!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_b,
                                    &channels.clone().flip()
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
                    match (packet.source_chain_id, packet.target_chain_id) {
                        (1, 2) => {
                            super::handlers::ibc_transfer_receive_packet(
                                chains.node_a.as_ref(),
                                chains.node_b.as_ref(),
                                &channels,
                                packet,
                            )?;
                            assert_eq!(
                                super::utils::get_acknowledged_packets_at_dst(
                                    &chains.handle_b,
                                    &channels.clone().flip()
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
                                &channels.clone().flip(),
                                packet,
                            )?;
                            assert_eq!(
                                super::utils::get_acknowledged_packets_at_dst(
                                    &chains.handle_a,
                                    &channels
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
                    match (packet.source_chain_id, packet.target_chain_id) {
                        (1, 2) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_a,
                                    &channels
                                )?
                                .is_empty(),
                                "commitment is completed"
                            );
                        }
                        (2, 1) => {
                            assert!(
                                super::utils::get_committed_packets_at_src(
                                    &chains.handle_b,
                                    &channels.clone().flip()
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

                    match (packet.source_chain_id, packet.target_chain_id) {
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
