use tracing::{debug, error};

use ibc::{
    ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
    ics03_connection::connection::{IdentifiedConnectionEnd, State as ConnectionState},
    ics04_channel::channel::IdentifiedChannelEnd,
    ics24_host::identifier::{ChainId, ConnectionId},
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

pub struct SpawnContext<'a> {
    config: &'a Config,
    registry: &'a mut Registry,
    workers: &'a mut WorkerMap,
}

impl<'a> SpawnContext<'a> {
    pub fn new(config: &'a Config, registry: &'a mut Registry, workers: &'a mut WorkerMap) -> Self {
        Self {
            config,
            registry,
            workers,
        }
    }

    pub fn spawn_workers(&mut self) {
        let chain_ids = self.config.chains.iter().map(|c| &c.id);
        for chain_id in chain_ids {
            self.spawn_workers_for_chain(chain_id);
        }
    }

    pub fn spawn_workers_for_chain(&mut self, chain_id: &ChainId) {
        let clients_req = QueryClientStatesRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let chain = match self.registry.get_or_spawn(chain_id) {
            Ok(chain_handle) => chain_handle,
            Err(e) => {
                error!(
                    "skipping workers for chain {}, reason: failed to spawn chain runtime with error: {}",
                    chain_id, e
                );

                return;
            }
        };

        let clients = match chain.query_clients(clients_req) {
            Ok(clients) => clients,
            Err(e) => {
                error!(
                    "skipping workers for chain {}, reason: failed to query clients with error: {}",
                    chain_id, e
                );

                return;
            }
        };

        for client in clients {
            self.spawn_workers_for_client(chain.clone(), client);
        }
    }

    pub fn spawn_workers_for_client(
        &mut self,
        chain: Box<dyn ChainHandle>,
        client: IdentifiedAnyClientState,
    ) {
        let counterparty_chain_id = client.client_state.chain_id();
        if self.config.find_chain(&counterparty_chain_id).is_none() {
            return;
        }

        let chain_id = chain.id();

        let conns_req = QueryClientConnectionsRequest {
            client_id: client.client_id.to_string(),
        };

        let client_connections = match chain.query_client_connections(conns_req) {
            Ok(connections) => connections,
            Err(e) => {
                error!(
                "skipping workers for chain {}, reason: failed to query client connections for client {}: {}",
                chain_id, client.client_id, e
            );

                return;
            }
        };

        for connection_id in client_connections {
            self.spawn_workers_for_connection(chain.clone(), &client, connection_id);
        }
    }

    pub fn spawn_workers_for_connection(
        &mut self,
        chain: Box<dyn ChainHandle>,
        client: &IdentifiedAnyClientState,
        connection_id: ConnectionId,
    ) {
        let connection_end = match chain.query_connection(&connection_id, Height::zero()) {
            Ok(connection_end) => connection_end,
            Err(e) => {
                error!(
                "skipping workers for chain {} and connection {}, reason: failed to query connection end: {}",
                chain.id(), connection_id, e
            );

                return;
            }
        };

        if !connection_end.state_matches(&ConnectionState::Open) {
            return;
        }

        let chans_req = QueryConnectionChannelsRequest {
            connection: connection_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let connection_channels = match chain.query_connection_channels(chans_req) {
            Ok(channels) => channels,
            Err(e) => {
                error!(
                "skipping workers for chain {} and connection {}, reason: failed to query its channels: {}",
                chain.id(), connection_id, e
            );

                return;
            }
        };

        let connection = IdentifiedConnectionEnd::new(connection_id, connection_end);

        for channel in connection_channels {
            let channel_id = channel.channel_id.clone();

            match self.spawn_workers_for_channel(chain.clone(), &client, &connection, channel) {
                Ok(()) => debug!(
                    "done spawning workers for chain {} and channel {}",
                    chain.id(),
                    channel_id,
                ),
                Err(e) => error!(
                    "skipped workers for chain {} and channel {} due to error {}",
                    chain.id(),
                    channel_id,
                    e
                ),
            }
        }
    }

    /// Spawns all the [`Worker`]s that will handle a given channel for a given source chain.
    pub fn spawn_workers_for_channel(
        &mut self,
        chain: Box<dyn ChainHandle>,
        client: &IdentifiedAnyClientState,
        connection: &IdentifiedConnectionEnd,
        channel: IdentifiedChannelEnd,
    ) -> Result<(), Error> {
        let counterparty_chain = self
            .registry
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

            self.workers
                .get_or_spawn(client_object, counterparty_chain.clone(), chain.clone());

            // TODO: Only start the Uni worker if there are outstanding packets or ACKs.
            //  https://github.com/informalsystems/ibc-rs/issues/901
            // create the path object and spawn worker
            let path_object = Object::UnidirectionalChannelPath(UnidirectionalChannelPath {
                dst_chain_id: counterparty_chain.id(),
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id,
                src_port_id: channel.port_id,
            });

            self.workers
                .get_or_spawn(path_object, chain, counterparty_chain);
        } else if !chan_state_dst.is_open()
            && chan_state_dst.less_or_equal_progress(chan_state_src)
            && self.config.handshake_enabled()
        {
            // create worker for channel handshake that will advance the remote state
            let channel_object = Object::Channel(Channel {
                dst_chain_id: counterparty_chain.id(),
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id,
                src_port_id: channel.port_id,
            });

            self.workers
                .get_or_spawn(channel_object, chain, counterparty_chain);
        }

        Ok(())
    }
}
