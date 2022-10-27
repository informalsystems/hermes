use std::io::Write;
use std::panic::{RefUnwindSafe, UnwindSafe};

use ibc_relayer::config::{
    Channels as ConfigChannels, Clients as ConfigClients, Connections as ConfigConnections,
    ModeConfig, Packets as ConfigPackets,
};

use ibc_test_framework::prelude::*;
use ibc_test_framework::types::tagged::mono::Tagged;

use super::state::{Action, State};

use super::itf::InformalTrace;
use super::utils::{get_chain, CLIENT_EXPIRY};

const TEST_NAMES: &[&str] = &[
    "LocalTransferInv",
    "IBCTransferAcknowledgePacketInv",
    "IBCTransferTimeoutPacketInv",
];
const NUM_TRACES: Option<&str> = option_env!("MBT_TRACES");
const APALACHE: Option<&str> = option_env!("APALACHE");

const ITF_TRACE_DIRECTORY: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/data/mbt");

fn generate_mbt_traces(
    apalache_path: &str,
    test_name: &str,
    num_traces: usize,
) -> Result<Vec<(String, String)>, Error> {
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

    std::fs::read_dir(run_dir)?
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
                    .then(|| {
                        let name = format!("{test_name}_{file_name}");
                        Ok((
                            name,
                            std::fs::read_to_string(file_path.to_str().expect("should not panic"))
                                .expect("error while reading counterexample.itf.json"),
                        ))
                    })
                })
        })
        .collect()
}

fn execute_mbt<F>(f: F) -> Result<(), Error>
where
    F: FnOnce(Vec<State>) -> Result<(), Error> + UnwindSafe + RefUnwindSafe + Copy,
{
    let apalache = APALACHE.unwrap_or("apalache-mc");
    let num_traces = NUM_TRACES
        .unwrap_or("2")
        .parse()
        .expect("an number for number of traces per test");

    let success_traces = &format!("{ITF_TRACE_DIRECTORY}/success");
    let failure_traces = &format!("{ITF_TRACE_DIRECTORY}/failure");

    std::fs::create_dir_all(success_traces)?;
    std::fs::create_dir_all(failure_traces)?;

    for test_name in TEST_NAMES {
        for (itf_name, itf_json) in generate_mbt_traces(apalache, test_name, num_traces)? {
            let itf: InformalTrace<State> =
                serde_json::from_str(&itf_json).expect("deserialization error");

            let result = std::panic::catch_unwind(|| f(itf.states).expect("to fail"));

            let unique_itf_trace_path = if result.is_ok() {
                format!("{success_traces}/{itf_name}")
            } else {
                format!("{failure_traces}/{itf_name}")
            };

            let mut file = std::fs::File::create(unique_itf_trace_path)?;
            file.write_all(itf_json.as_bytes())?;

            if let Err(err) = result {
                std::panic::resume_unwind(err);
            }
        }
    }
    Ok(())
}

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    execute_mbt(|trace| run_binary_channel_test(&IbcTransferMBT(trace)))
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

    execute_mbt(|trace| {
        run_self_connected_binary_chain_test(&RunBinaryConnectionTest::new(
            &RunBinaryChannelTest::new(&IbcTransferMBT(trace)),
        ))
    })
}

pub struct IbcTransferMBT(Vec<State>);

impl TestOverrides for IbcTransferMBT {
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
                ..Default::default()
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
                    if supervisor.is_none() {
                        supervisor = Some(relayer.spawn_supervisor()?);
                    }

                    info!("[RestoreRelay] Done");
                }
                Action::InterruptRelay => {
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
