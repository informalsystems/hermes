use itertools::Itertools;
use tracing::{debug, error};

use ibc::{
    ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
    ics03_connection::connection::{IdentifiedConnectionEnd, State as ConnectionState},
    ics04_channel::channel::IdentifiedChannelEnd,
    Height,
};
use ibc_proto::ibc::core::{
    channel::v1::QueryConnectionChannelsRequest, client::v1::QueryClientStatesRequest,
    connection::v1::QueryClientConnectionsRequest,
};

use crate::{
    chain::{counterparty::channel_state_on_destination, handle::ChainHandle},
    config::Config,
    object::{Channel, Client, Object, UnidirectionalChannelPath},
    registry::Registry,
    worker::WorkerMap,
};

use super::Error;

pub fn spawn_workers(config: &Config, registry: &mut Registry, workers: &mut WorkerMap) {
    let clients_req = QueryClientStatesRequest {
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let chain_ids = config.chains.iter().map(|c| c.id.clone()).collect_vec();

    for chain_id in chain_ids {
        let chain = match registry.get_or_spawn(&chain_id) {
            Ok(chain_handle) => chain_handle,
            Err(e) => {
                error!(
                    "skipping workers for chain {}. \
                        reason: failed to spawn chain runtime with error: {}",
                    chain_id, e
                );

                continue;
            }
        };

        let clients = match chain.query_clients(clients_req.clone()) {
            Ok(clients) => clients,
            Err(e) => {
                error!(
                    "skipping workers for chain {}. \
                        reason: failed to query clients with error: {}",
                    chain_id, e
                );

                continue;
            }
        };

        for client in clients {
            let counterparty_chain_id = client.client_state.chain_id();
            if config.find_chain(&counterparty_chain_id).is_none() {
                continue;
            }

            let conns_req = QueryClientConnectionsRequest {
                client_id: client.client_id.to_string(),
            };

            let client_connections = match chain.query_client_connections(conns_req) {
                Ok(connections) => connections,
                Err(e) => {
                    error!(
                        "skipping workers for chain {}. \
                             reason: failed to query client connections for client {}: {}",
                        chain_id, client.client_id, e
                    );

                    continue;
                }
            };

            for connection_id in client_connections {
                let connection_end = match chain.query_connection(&connection_id, Height::zero()) {
                    Ok(connection_end) => connection_end,
                    Err(e) => {
                        error!(
                            "skipping workers for chain {} and connection {}. \
                                    reason: failed to query connection end: {}",
                            chain_id, connection_id, e
                        );

                        continue;
                    }
                };

                if !connection_end.state_matches(&ConnectionState::Open) {
                    continue;
                }

                let chans_req = QueryConnectionChannelsRequest {
                    connection: connection_id.to_string(),
                    pagination: ibc_proto::cosmos::base::query::pagination::all(),
                };

                let connection_channels = match chain.query_connection_channels(chans_req) {
                    Ok(channels) => channels,
                    Err(e) => {
                        error!(
                            "skipping workers for chain {} and connection {}. \
                                     reason: failed to query its channels: {}",
                            chain_id, connection_id, e
                        );

                        continue;
                    }
                };

                let connection =
                    IdentifiedConnectionEnd::new(connection_id.clone(), connection_end);

                for channel in connection_channels {
                    match spawn_channel_workers(
                        config,
                        registry,
                        workers,
                        chain.clone(),
                        client.clone(),
                        connection.clone(),
                        channel.clone(),
                    ) {
                        Ok(()) => debug!(
                            "done spawning workers for chain {} and channel {}",
                            chain.id(),
                            channel.channel_id
                        ),
                        Err(e) => error!(
                            "skipped workers for chain {} and channel {} due to error {}",
                            chain.id(),
                            channel.channel_id,
                            e
                        ),
                    }
                }
            }
        }
    }
}

/// Spawns all the [`Worker`]s that will handle a given channel for a given source chain.
fn spawn_channel_workers(
    config: &Config,
    registry: &mut Registry,
    workers: &mut WorkerMap,
    chain: Box<dyn ChainHandle>,
    client: IdentifiedAnyClientState,
    connection: IdentifiedConnectionEnd,
    channel: IdentifiedChannelEnd,
) -> Result<(), Error> {
    let counterparty_chain = registry
        .get_or_spawn(&client.client_state.chain_id())
        .map_err(|e| Error::FailedToSpawnChainRuntime(e.to_string()))?;

    let chan_state_src = channel.channel_end.state;
    let chan_state_dst =
        channel_state_on_destination(&channel, &connection, counterparty_chain.as_ref())?;

    debug!(
        "channel {} on chain {} is: {}; state on dest. chain ({}) is: {}",
        channel.channel_id,
        chain.id(),
        chan_state_src,
        counterparty_chain.id(),
        chan_state_dst
    );

    if chan_state_src.is_open() && chan_state_dst.is_open() {
        // create the client object and spawn worker
        let client_object = Object::Client(Client {
            dst_client_id: client.client_id.clone(),
            dst_chain_id: chain.id(),
            src_chain_id: client.client_state.chain_id(),
        });

        workers.get_or_spawn(client_object, counterparty_chain.clone(), chain.clone());

        // TODO: Only start the Uni worker if there are outstanding packets or ACKs.
        //  https://github.com/informalsystems/ibc-rs/issues/901
        // create the path object and spawn worker
        let path_object = Object::UnidirectionalChannelPath(UnidirectionalChannelPath {
            dst_chain_id: counterparty_chain.clone().id(),
            src_chain_id: chain.id(),
            src_channel_id: channel.channel_id.clone(),
            src_port_id: channel.port_id,
        });

        workers.get_or_spawn(path_object, chain.clone(), counterparty_chain.clone());
    } else if !chan_state_dst.is_open()
        && chan_state_dst as u32 <= chan_state_src as u32
        && config.handshake_enabled()
    {
        // create worker for channel handshake that will advance the remote state
        let channel_object = Object::Channel(Channel {
            dst_chain_id: counterparty_chain.clone().id(),
            src_chain_id: chain.id(),
            src_channel_id: channel.channel_id.clone(),
            src_port_id: channel.port_id,
        });

        workers.get_or_spawn(channel_object, chain.clone(), counterparty_chain.clone());
    }

    Ok(())
}
