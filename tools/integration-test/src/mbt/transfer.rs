use ibc_relayer::config::{
    Channels as ConfigChannels, Clients as ConfigClients, Connections as ConfigConnections,
    ModeConfig, Packets as ConfigPackets,
};
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle, SupervisorOptions};
use ibc_relayer::worker::client::spawn_refresh_client;

use crate::bootstrap::binary::connection::bootstrap_connection;
use crate::framework::binary::chain::run_self_connected_binary_chain_test;
use crate::prelude::*;
use crate::types::tagged::mono::Tagged;

use super::state::Action;

use super::utils::{get_chain, parse_itf_from_json, wait_for_client_expiry, CLIENT_EXPIRY};

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
    fn run<Chain1: ChainHandle, Chain2: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<Chain1, Chain2>,
    ) -> Result<(), Error> {
        let itf_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/spec/example/counterexample.itf.json"
        );

        // bootstrapping connection before relayer is spawned
        {
            let _refresh_task_a = spawn_refresh_client(chains.client_b_to_a.clone())
                .ok_or_else(|| eyre!("expect refresh task spawned"))?;

            let _refresh_task_b = spawn_refresh_client(chains.client_a_to_b.clone())
                .ok_or_else(|| eyre!("expect refresh task spawned"))?;

            bootstrap_connection(&chains.client_b_to_a, &chains.client_a_to_b, false)?;
        };

        wait_for_client_expiry();

        let mut channels = None;
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
                    info!("[Init] Initial State");
                }
                Action::LocalTransfer {
                    chain_id,
                    source,
                    target,
                    denom,
                    amount,
                } => {
                    let node: Tagged<Chain1, _> = get_chain(&chains, chain_id);
                    super::handlers::local_transfer_handler(node, source, target, denom, amount)?;
                }
                Action::CreateChannel { chains: chain_pair } => {
                    assert_eq!(chain_pair.0.len(), 2);
                    assert!(chain_pair.0.contains(&1));
                    assert!(chain_pair.0.contains(&2));

                    let chain_handle_a = &chains.handle_a;
                    let chain_handle_b = &chains.handle_b;

                    super::handlers::create_channel(
                        chain_handle_a,
                        chain_handle_b,
                        &mut channels,
                        &mut refresh_task_a,
                        &mut refresh_task_b,
                    )?;
                }
                Action::ExpireChannel { chains: chain_pair } => {
                    assert_eq!(chain_pair.0.len(), 2);
                    assert!(chain_pair.0.contains(&1));
                    assert!(chain_pair.0.contains(&2));

                    super::handlers::expire_channel(
                        &mut channels,
                        &mut refresh_task_a,
                        &mut refresh_task_b,
                    )?;
                }
                Action::IBCTransferSendPacket { packet } => {
                    let node_source: Tagged<Chain1, _> =
                        get_chain(&chains, packet.channel.source.chain_id);
                    let node_target: Tagged<Chain2, _> =
                        get_chain(&chains, packet.channel.target.chain_id);

                    super::handlers::ibc_transfer_send_packet(
                        node_source,
                        node_target,
                        &channels,
                        &packet,
                    )?;
                }
                Action::IBCTransferReceivePacket { packet } => {
                    let node_source: Tagged<Chain1, _> =
                        get_chain(&chains, packet.channel.source.chain_id);
                    let node_target: Tagged<Chain2, _> =
                        get_chain(&chains, packet.channel.target.chain_id);

                    super::handlers::ibc_transfer_receive_packet(
                        node_source,
                        node_target,
                        &channels,
                        &packet,
                    )?;
                }
                Action::IBCTransferAcknowledgePacket { packet } => {
                    let node_source: Tagged<Chain1, _> =
                        get_chain(&chains, packet.channel.source.chain_id);
                    let node_target: Tagged<Chain2, _> =
                        get_chain(&chains, packet.channel.target.chain_id);

                    super::handlers::ibc_transfer_acknowledge_packet(
                        node_source,
                        node_target,
                        &channels,
                        &packet,
                    )?;
                }
                Action::IBCTransferTimeoutPacket { .. } => {
                    // TODO: make sure channel is expired before sending the packet
                    // TODO: the source account blance will be refunded
                    info!("[IBCTransferTimeoutPacket] Packet timeout is not supported")
                }
            }
        }

        Ok(())
    }
}
