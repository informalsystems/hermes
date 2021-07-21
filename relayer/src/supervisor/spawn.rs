use anomaly::BoxError;
use itertools::Itertools;
use tracing::{debug, error, warn};

use ibc::{
    ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
    ics03_connection::connection::{IdentifiedConnectionEnd, State as ConnectionState},
    ics04_channel::channel::{IdentifiedChannelEnd, State as ChannelState},
    ics24_host::identifier::{ChainId, ConnectionId},
    Height,
};

use ibc_proto::ibc::core::{
    channel::v1::QueryConnectionChannelsRequest, client::v1::QueryClientStatesRequest,
    connection::v1::QueryClientConnectionsRequest,
};

use crate::{
    chain::{
        counterparty::{channel_on_destination, connection_state_on_destination},
        handle::ChainHandle,
    },
    config::Config,
    object::{Channel, Client, Connection, Object, Packet},
    registry::Registry,
    supervisor::client_state_filter::{FilterPolicy, Permission},
    worker::WorkerMap,
};

use super::{Error, RwArc};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SpawnMode {
    Startup,
    Reload,
}

/// A context for spawning workers within the [`crate::supervisor::Supervisor`].
pub struct SpawnContext<'a> {
    config: &'a RwArc<Config>,
    registry: &'a mut Registry,
    workers: &'a mut WorkerMap,
    client_state_filter: &'a mut FilterPolicy,
    mode: SpawnMode,
}

impl<'a> SpawnContext<'a> {
    pub fn new(
        config: &'a RwArc<Config>,
        registry: &'a mut Registry,
        client_state_filter: &'a mut FilterPolicy,
        workers: &'a mut WorkerMap,
        mode: SpawnMode,
    ) -> Self {
        Self {
            config,
            registry,
            workers,
            client_state_filter,
            mode,
        }
    }

    fn client_filter_enabled(&self) -> bool {
        // Currently just a wrapper over the global filter.
        self.config.read().expect("poisoned lock").global.filter
    }

    pub fn spawn_workers(&mut self) {
        let chain_ids = self
            .config
            .read()
            .expect("poisoned lock")
            .chains
            .iter()
            .map(|c| &c.id)
            .cloned()
            .collect_vec();

        for chain_id in chain_ids {
            self.spawn_workers_for_chain(&chain_id);
        }
    }

    pub fn spawn_workers_from_chain_to_chain(
        &mut self,
        from_chain_id: &ChainId,
        to_chain_id: &ChainId,
    ) {
        let clients_req = QueryClientStatesRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let chain = match self.registry.get_or_spawn(from_chain_id) {
            Ok(chain_handle) => chain_handle,
            Err(e) => {
                error!(
                    "skipping workers for chain {}, reason: failed to spawn chain runtime with error: {}",
                    from_chain_id, e
                );

                return;
            }
        };

        let clients = match chain.query_clients(clients_req) {
            Ok(clients) => clients,
            Err(e) => {
                error!(
                    "skipping workers for chain {}, reason: failed to query clients with error: {}",
                    from_chain_id, e
                );

                return;
            }
        };

        for client in clients {
            if &client.client_state.chain_id() == to_chain_id {
                self.spawn_workers_for_client(chain.clone(), client);
            }
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

        if self.mode != SpawnMode::Reload {
            return;
        }

        let chain_ids = self
            .config
            .read()
            .expect("poisoned lock")
            .chains
            .iter()
            .map(|c| &c.id)
            .cloned()
            .collect_vec();

        for id in chain_ids {
            if chain_id == &id {
                continue;
            }
            self.spawn_workers_from_chain_to_chain(&id, &chain_id);
        }
    }

    pub fn spawn_workers_for_client(
        &mut self,
        chain: Box<dyn ChainHandle>,
        client: IdentifiedAnyClientState,
    ) {
        // Potentially ignore the client
        if self.client_filter_enabled()
            && matches!(
                self.client_state_filter.control_client(
                    &chain.id(),
                    &client.client_id,
                    &client.client_state
                ),
                Permission::Deny
            )
        {
            warn!(
                "skipping workers for chain {}, client {}. \
                             reason: client is not allowed (client trust level={:?})",
                chain.id(),
                client.client_id,
                client.client_state.trust_threshold()
            );

            return;
        }

        let counterparty_chain_id = client.client_state.chain_id();
        let has_counterparty = self
            .config
            .read()
            .expect("poisoned lock")
            .has_chain(&counterparty_chain_id);

        if !has_counterparty {
            debug!(
                "skipping client worker for client {} on chain {} has its counterparty ({}) is not present in config",
                client.client_id, chain.id(), counterparty_chain_id
            );

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
        let chain_id = chain.id();

        let connection_end = match chain.query_connection(&connection_id, Height::zero()) {
            Ok(connection_end) => connection_end,
            Err(e) => {
                error!(
                    "skipping workers for chain {} and connection {}, reason: failed to query connection end: {}",
                    chain_id, connection_id, e
                );
                return;
            }
        };

        let connection = IdentifiedConnectionEnd {
            connection_id: connection_id.clone(),
            connection_end: connection_end.clone(),
        };

        // Apply the client state filter
        if self.client_filter_enabled() {
            match self.client_state_filter.control_connection_end_and_client(
                &mut self.registry,
                &chain_id,
                &client.client_state,
                &connection_end,
                &connection_id,
            ) {
                Ok(Permission::Deny) => {
                    warn!(
                        "skipping workers for chain {}, client {} & conn {}. \
                                 reason: client or counterparty client is not allowed",
                        chain_id, client.client_id, connection_id
                    );
                    return;
                }
                Err(e) => {
                    error!("skipping workers for chain {}. reason: {}", chain_id, e);
                    return;
                }
                _ => {} // allowed
            }
        }

        match self.spawn_connection_workers(chain.clone(), client.clone(), connection.clone()) {
            Ok(()) => debug!(
                "done spawning workers for connection {} on chain {}",
                connection.connection_id,
                chain.id(),
            ),
            Err(e) => error!(
                "skipped workers for connection {} on chain {} due to error {}",
                chain.id(),
                connection.connection_id,
                e
            ),
        }

        if !connection_end.is_open() {
            debug!(
                "connection {} not open, skip workers for channels over this connection",
                connection.connection_id
            );
            return;
        }

        let connection = IdentifiedConnectionEnd {
            connection_id: connection_id.clone(),
            connection_end: connection_end.clone(),
        };

        match self.counterparty_connection_state(client.clone(), connection.clone()) {
            Err(e) => {
                debug!("error with counterparty: reason {}", e);
                return;
            }
            Ok(state) => {
                if !state.eq(&ConnectionState::Open) {
                    debug!(
                        "connection {} not open, skip workers for channels over this connection",
                        connection.connection_id
                    );

                    debug!(
                        "drop connection {} because its counterparty is not open",
                        connection_id
                    );

                    return;
                }
            }
        };

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

    fn counterparty_connection_state(
        &mut self,
        client: IdentifiedAnyClientState,
        connection: IdentifiedConnectionEnd,
    ) -> Result<ConnectionState, BoxError> {
        let counterparty_chain = self
            .registry
            .get_or_spawn(&client.client_state.chain_id())?;

        Ok(connection_state_on_destination(
            connection,
            counterparty_chain.as_ref(),
        )?)
    }

    fn spawn_connection_workers(
        &mut self,
        chain: Box<dyn ChainHandle>,
        client: IdentifiedAnyClientState,
        connection: IdentifiedConnectionEnd,
    ) -> Result<(), BoxError> {
        let handshake_enabled = self
            .config
            .read()
            .expect("poisoned lock")
            .handshake_enabled();

        let counterparty_chain = self
            .registry
            .get_or_spawn(&client.client_state.chain_id())?;

        let conn_state_src = connection.connection_end.state;
        let conn_state_dst =
            connection_state_on_destination(connection.clone(), counterparty_chain.as_ref())?;

        debug!(
            "connection {} on chain {} is: {:?}, state on dest. chain ({}) is: {:?}",
            connection.connection_id,
            chain.id(),
            conn_state_src,
            counterparty_chain.id(),
            conn_state_dst
        );

        if conn_state_src.is_open() && conn_state_dst.is_open() {
            debug!(
                "connection {} on chain {} is already open, not spawning Client worker",
                connection.connection_id,
                chain.id()
            );
        } else if !conn_state_dst.is_open()
            && conn_state_dst.less_or_equal_progress(conn_state_src)
            && handshake_enabled
        {
            // create worker for connection handshake that will advance the remote state
            let connection_object = Object::Connection(Connection {
                dst_chain_id: client.client_state.chain_id(),
                src_chain_id: chain.id(),
                src_connection_id: connection.connection_id,
            });

            self.workers
                .spawn(
                    chain.clone(),
                    counterparty_chain.clone(),
                    &connection_object,
                    &self.config.read().expect("poisoned lock"),
                )
                .then(|| {
                    debug!(
                        "spawning Connection worker: {}",
                        connection_object.short_name()
                    );
                });
        }

        Ok(())
    }

    /// Spawns all the [`Worker`]s that will handle a given channel for a given source chain.
    pub fn spawn_workers_for_channel(
        &mut self,
        chain: Box<dyn ChainHandle>,
        client: &IdentifiedAnyClientState,
        connection: &IdentifiedConnectionEnd,
        channel: IdentifiedChannelEnd,
    ) -> Result<(), Error> {
        let handshake_enabled = self
            .config
            .read()
            .expect("poisoned lock")
            .handshake_enabled();

        let counterparty_chain = self
            .registry
            .get_or_spawn(&client.client_state.chain_id())
            .map_err(|e| Error::FailedToSpawnChainRuntime(e.to_string()))?;

        let counterparty_channel =
            channel_on_destination(&channel, &connection, counterparty_chain.as_ref())?;

        let chan_state_src = channel.channel_end.state;
        let chan_state_dst = counterparty_channel
            .as_ref()
            .map_or(ChannelState::Uninitialized, |c| c.state);

        debug!(
            "channel {} on chain {} is: {}; state on dest. chain ({}) is: {}",
            channel.channel_id,
            chain.id(),
            chan_state_src,
            counterparty_chain.id(),
            chan_state_dst
        );

        if chan_state_src.is_open()
            && chan_state_dst.is_open()
            && self.relay_packets_on_channel(chain.as_ref(), &channel)
        {
            // spawn the client worker
            let client_object = Object::Client(Client {
                dst_client_id: client.client_id.clone(),
                dst_chain_id: chain.id(),
                src_chain_id: client.client_state.chain_id(),
            });

            self.workers
                .spawn(
                    counterparty_chain.clone(),
                    chain.clone(),
                    &client_object,
                    &self.config.read().expect("poisoned lock"),
                )
                .then(|| debug!("spawned Client worker: {}", client_object.short_name()));

            // create the Packet object and spawn worker
            let path_object = Object::Packet(Packet {
                dst_chain_id: counterparty_chain.id(),
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id,
                src_port_id: channel.port_id,
            });

            self.workers
                .spawn(
                    chain.clone(),
                    counterparty_chain.clone(),
                    &path_object,
                    &self.config.read().expect("poisoned lock"),
                )
                .then(|| debug!("spawned Path worker: {}", path_object.short_name()));
        } else if !chan_state_dst.is_open()
            && chan_state_dst.less_or_equal_progress(chan_state_src)
            && handshake_enabled
        {
            // create worker for channel handshake that will advance the remote state
            let channel_object = Object::Channel(Channel {
                dst_chain_id: counterparty_chain.id(),
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id,
                src_port_id: channel.port_id,
            });

            self.workers
                .spawn(
                    chain,
                    counterparty_chain,
                    &channel_object,
                    &self.config.read().expect("poisoned lock"),
                )
                .then(|| debug!("spawned Channel worker: {}", channel_object.short_name()));
        }

        Ok(())
    }

    fn relay_packets_on_channel(
        &mut self,
        chain: &dyn ChainHandle,
        channel: &IdentifiedChannelEnd,
    ) -> bool {
        let config = self.config.read().expect("poisoned lock");
        config.packets_on_channel_allowed(&chain.id(), &channel.port_id, &channel.channel_id)
    }

    pub fn shutdown_workers_for_chain(&mut self, chain_id: &ChainId) {
        let affected_workers = self.workers.objects_for_chain(chain_id);
        for object in affected_workers {
            self.workers.shutdown_worker(&object);
        }
    }
}
