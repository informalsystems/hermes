use core::fmt;
use std::collections::BTreeMap;

use itertools::Itertools;
use tracing::{debug, error, info, info_span, warn};

use ibc::{
    core::{
        ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
        ics03_connection::connection::{IdentifiedConnectionEnd, State as ConnectionState},
        ics04_channel::channel::{IdentifiedChannelEnd, State as ChannelState},
        ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    },
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
    config::{ChainConfig, ChannelsSpec, Config, PacketFilter},
    registry::Registry,
    supervisor::client_state_filter::{FilterPolicy, Permission},
};

use crate::chain::counterparty::{unreceived_acknowledgements, unreceived_packets};

use crate::error::Error as RelayerError;
use crate::registry::SpawnError;

flex_error::define_error! {
    Error {
        Spawn
            [ SpawnError ]
            |_| { "spawn" },

        Query
            [ RelayerError ]
            |_| { "query" },

        MissingConnectionHop
            {
                port_id: PortId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format_args!(
                    "could not retrieve the connection hop underlying port/channel {}/{} on chain '{}'",
                    e.port_id, e.channel_id, e.chain_id
                )
            },

        UninitializedChannel
            {
                port_id: PortId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format_args!(
                    "channel '{}/{}' on chain '{}' is uninitialized",
                    e.port_id, e.channel_id, e.chain_id
                )
            },

        CounterpartyConnectionState
            {
                connection_id: ConnectionId,
                counterparty_chain_id: ChainId,
                reason: String,
            }
            |e| {
                format_args!(
                    "failed to query counterparty connection state of connection '{}' on counterparty chain '{}', reason: {}",
                    e.connection_id, e.counterparty_chain_id, e.reason
                )
            }
    }
}

#[derive(Debug)]
pub struct ChainsScan {
    pub chains: Vec<Result<ChainScan, Error>>,
}

impl fmt::Display for ChainsScan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for scan in self.chains.iter().flatten() {
            writeln!(f, "# Chain: {}", scan.chain_id)?;

            for client in scan.clients.values() {
                writeln!(f, "  - Client: {}", client.client.client_id)?;

                for conn in client.connections.values() {
                    let counterparty = conn
                        .counterparty_state
                        .as_ref()
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| "<none>".to_string());

                    writeln!(f, "    * Connection: {}", conn.connection.connection_id)?;
                    writeln!(f, "      | State: {}", conn.state())?;
                    writeln!(f, "      | Counterparty state: {}", counterparty)?;

                    for chan in conn.channels.values() {
                        let counterparty = chan
                            .counterparty
                            .as_ref()
                            .map(|c| c.channel_id.to_string())
                            .unwrap_or_else(|| "<none>".to_string());

                        writeln!(f, "      + Channel: {}", chan.channel.channel_id)?;
                        writeln!(f, "        | Port: {}", chan.channel.port_id)?;
                        writeln!(f, "        | State: {}", chan.channel.channel_end.state())?;
                        writeln!(f, "        | Counterparty: {}", counterparty)?;
                    }
                }
            }
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct ChainScan {
    pub chain_id: ChainId,
    pub clients: BTreeMap<ClientId, ClientScan>,
}

impl ChainScan {
    fn new(chain_id: ChainId) -> ChainScan {
        Self {
            chain_id,
            clients: BTreeMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ClientScan {
    pub client: IdentifiedAnyClientState,
    pub connections: BTreeMap<ConnectionId, ConnectionScan>,
}

impl ClientScan {
    fn new(client: IdentifiedAnyClientState) -> ClientScan {
        Self {
            client,
            connections: BTreeMap::new(),
        }
    }

    pub fn id(&self) -> &ClientId {
        &self.client.client_id
    }

    pub fn counterparty_chain_id(&self) -> ChainId {
        self.client.client_state.chain_id()
    }
}

#[derive(Clone, Debug)]
pub struct ConnectionScan {
    pub connection: IdentifiedConnectionEnd,
    pub counterparty_state: Option<ConnectionState>,
    pub channels: BTreeMap<ChannelId, ChannelScan>,
}

impl ConnectionScan {
    pub fn new(
        connection: IdentifiedConnectionEnd,
        counterparty_state: Option<ConnectionState>,
    ) -> Self {
        Self {
            connection,
            counterparty_state,
            channels: BTreeMap::new(),
        }
    }

    pub fn id(&self) -> &ConnectionId {
        &self.connection.connection_id
    }

    pub fn state(&self) -> ConnectionState {
        self.connection.connection_end.state
    }

    pub fn is_open(&self) -> bool {
        self.connection.connection_end.is_open()
    }
}

#[derive(Clone, Debug)]
pub struct ChannelScan {
    pub channel: IdentifiedChannelEnd,
    pub counterparty: Option<IdentifiedChannelEnd>,
}

impl ChannelScan {
    pub fn new(channel: IdentifiedChannelEnd, counterparty: Option<IdentifiedChannelEnd>) -> Self {
        Self {
            channel,
            counterparty,
        }
    }

    pub fn id(&self) -> &ChannelId {
        &self.channel.channel_id
    }

    pub fn unreceived_packets_on_counterparty(
        &self,
        chain: &impl ChainHandle,
        counterparty_chain: &impl ChainHandle,
    ) -> Option<Vec<u64>> {
        self.counterparty.as_ref().map(|counterparty| {
            unreceived_packets(counterparty_chain, chain, counterparty).unwrap_or_default()
        })
    }

    pub fn unreceived_acknowledgements_on_counterparty(
        &self,
        chain: &impl ChainHandle,
        counterparty_chain: &impl ChainHandle,
    ) -> Option<Vec<u64>> {
        self.counterparty.as_ref().map(|counterparty| {
            unreceived_acknowledgements(counterparty_chain, chain, counterparty).unwrap_or_default()
        })
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ScanMode {
    Auto,
    Full,
}

pub struct ChainScanner<'a, Chain: ChainHandle> {
    config: &'a Config,
    registry: &'a mut Registry<Chain>,
    client_state_filter: &'a mut FilterPolicy,
    scan_mode: ScanMode,
}

impl<'a, Chain: ChainHandle> ChainScanner<'a, Chain> {
    pub fn new(
        config: &'a Config,
        registry: &'a mut Registry<Chain>,
        client_state_filter: &'a mut FilterPolicy,
        scan_mode: ScanMode,
    ) -> Self {
        Self {
            config,
            registry,
            client_state_filter,
            scan_mode,
        }
    }

    pub fn scan_chains(mut self) -> ChainsScan {
        let mut scans = ChainsScan {
            chains: Vec::with_capacity(self.config.chains.len()),
        };

        for chain in self.config.chains.clone() {
            scans.chains.push(self.scan_chain(&chain));
        }

        scans
    }

    pub fn scan_chain(&mut self, chain_config: &ChainConfig) -> Result<ChainScan, Error> {
        let span = info_span!("scan.chain", chain = %chain_config.id);
        let _guard = span.enter();

        info!("scanning chain...");

        let chain = match self.registry.get_or_spawn(&chain_config.id) {
            Ok(chain_handle) => chain_handle,
            Err(e) => {
                error!(
                    "aborting scan, reason: failed to spawn chain runtime with error: {}",
                    e
                );

                return Err(Error::spawn(e));
            }
        };

        let mut scan = ChainScan::new(chain_config.id.clone());

        match self.use_allow_list(chain_config) {
            Some(spec) if self.scan_mode == ScanMode::Auto => {
                info!("chain uses an allow list, skipping scan for fast startup");
                info!("allowed ports/channels: {}", spec);

                self.query_allowed_channels(&chain, spec, &mut scan)?;
            }
            _ => {
                info!("scanning chain for all clients, connections and channels");
                self.scan_all_clients(&chain, &mut scan)?;
            }
        };

        Ok(scan)
    }

    pub fn query_allowed_channels(
        &mut self,
        chain: &Chain,
        spec: &ChannelsSpec,
        scan: &mut ChainScan,
    ) -> Result<(), Error> {
        info!("querying allowed channels...");

        for (port_id, channel_id) in spec.iter() {
            let result = scan_allowed_channel(self.registry, chain, port_id, channel_id);

            match result {
                Ok(ScannedChannel {
                    channel,
                    counterparty_channel,
                    connection,
                    counterparty_connection_state,
                    client,
                }) => {
                    let client_scan = scan
                        .clients
                        .entry(client.client_id.clone())
                        .or_insert_with(|| ClientScan::new(client));

                    let connection_scan = client_scan
                        .connections
                        .entry(connection.connection_id.clone())
                        .or_insert_with(|| {
                            ConnectionScan::new(connection, counterparty_connection_state)
                        });

                    connection_scan
                        .channels
                        .entry(channel.channel_id.clone())
                        .or_insert_with(|| ChannelScan::new(channel, counterparty_channel));
                }
                Err(e) => error!(channel = %channel_id, "failed to scan channel, reason: {}", e),
            }
        }

        Ok(())
    }

    pub fn scan_all_clients(&mut self, chain: &Chain, scan: &mut ChainScan) -> Result<(), Error> {
        info!("scanning all clients...");

        let clients = query_all_clients(chain)?;

        for client in clients {
            if let Some(client_scan) = self.scan_client(chain, client)? {
                scan.clients.insert(client_scan.id().clone(), client_scan);
            }
        }

        Ok(())
    }

    fn scan_client(
        &mut self,
        chain: &Chain,
        client: IdentifiedAnyClientState,
    ) -> Result<Option<ClientScan>, Error> {
        let span = info_span!("scan.client", client = %client.client_id);
        let _guard = span.enter();

        info!("scanning client...");

        if !self.client_allowed(chain, &client) {
            warn!(
                trust_threshold = ?client.client_state.trust_threshold(),
                "skipping client, reason: client is not allowed",
            );

            return Ok(None);
        }

        let counterparty_chain_id = client.client_state.chain_id();
        let has_counterparty = self.config.has_chain(&counterparty_chain_id);

        if !has_counterparty {
            debug!(
                chain = %chain.id(),
                counterparty_chain = %counterparty_chain_id,
                "skipping client because its counterparty is not present in the config",
            );

            return Ok(None);
        }

        let client_connections_ids = query_client_connections(chain, &client.client_id)?;

        let mut scan = ClientScan::new(client);

        for connection_end in client_connections_ids {
            if let Some(connection_scan) =
                self.scan_connection(chain, &scan.client, connection_end)?
            {
                scan.connections
                    .insert(connection_scan.id().clone(), connection_scan);
            }
        }

        Ok(Some(scan))
    }

    fn scan_connection(
        &mut self,
        chain: &Chain,
        client: &IdentifiedAnyClientState,
        connection: IdentifiedConnectionEnd,
    ) -> Result<Option<ConnectionScan>, Error> {
        let span = info_span!("scan.connection", connection = %connection.connection_id);
        let _guard = span.enter();

        info!("scanning connection...");

        if !self.connection_allowed(chain, client, &connection) {
            warn!("skipping connection, reason: connection is not allowed",);
            return Ok(None);
        }

        let mut scan = ConnectionScan::new(connection, None);

        if !scan.is_open() {
            warn!("connection is not open, skipping scan of channels over this connection");
            return Ok(Some(scan));
        }

        let counterparty_state = match self.counterparty_connection_state(client, &scan.connection)
        {
            Ok(state) if !state.eq(&ConnectionState::Open) => {
                warn!("counterparty connection is not open, skipping scan of channels over this connection");
                return Ok(Some(scan));
            }
            Err(e) => {
                error!("error fetching counterparty connection state: {}", e);
                return Ok(None);
            }
            Ok(state) => state,
        };

        scan.counterparty_state = Some(counterparty_state);

        let channels = match query_connection_channels(chain, scan.connection.id()) {
            Ok(channels) => channels,
            Err(e) => {
                error!("failed to fetch connection channels: {}", e);
                Vec::new()
            }
        };

        let counterparty_chain = self
            .registry
            .get_or_spawn(&client.client_state.chain_id())
            .map_err(Error::spawn)?;

        let channels = channels
            .into_iter()
            .filter(|channel| self.channel_allowed(chain, channel))
            .map(|channel| {
                let counterparty =
                    channel_on_destination(&channel, &scan.connection, &counterparty_chain)
                        .unwrap_or_default();

                let scan = ChannelScan {
                    channel,
                    counterparty,
                };

                (scan.id().clone(), scan)
            })
            .collect();

        scan.channels = channels;

        Ok(Some(scan))
    }

    fn counterparty_connection_state(
        &mut self,
        client: &IdentifiedAnyClientState,
        connection: &IdentifiedConnectionEnd,
    ) -> Result<ConnectionState, Error> {
        let counterparty_chain = self
            .registry
            .get_or_spawn(&client.client_state.chain_id())
            .map_err(Error::spawn)?;

        let counterparty_state = connection_state_on_destination(connection, &counterparty_chain)
            .map_err(|e| {
            Error::counterparty_connection_state(
                connection.connection_id.clone(),
                client.client_state.chain_id(),
                e.to_string(),
            )
        })?;

        Ok(counterparty_state)
    }

    fn filtering_enabled(&self) -> bool {
        // filtering is always enabled
        true
    }

    fn use_allow_list<'b>(&self, chain_config: &'b ChainConfig) -> Option<&'b ChannelsSpec> {
        if !self.filtering_enabled() {
            return None;
        }

        match chain_config.packet_filter {
            PacketFilter::Allow(ref spec) => Some(spec),
            _ => None,
        }
    }

    fn client_allowed(&mut self, chain: &Chain, client: &IdentifiedAnyClientState) -> bool {
        if !self.filtering_enabled() {
            return true;
        };

        let permission = self.client_state_filter.control_client(
            &chain.id(),
            &client.client_id,
            &client.client_state,
        );

        permission == Permission::Allow
    }

    fn connection_allowed(
        &mut self,
        chain: &Chain,
        client: &IdentifiedAnyClientState,
        connection: &IdentifiedConnectionEnd,
    ) -> bool {
        if !self.filtering_enabled() {
            return true;
        }

        let permission = self.client_state_filter.control_connection_end_and_client(
            self.registry,
            &chain.id(),
            &client.client_state,
            &connection.connection_end,
            &connection.connection_id,
        );

        match permission {
            Ok(Permission::Deny) => {
                warn!(
                    "skipping workers for chain {}, client {} & conn {}, \
                     reason: client or counterparty client is not allowed",
                    chain.id(),
                    client.client_id,
                    connection.connection_id
                );

                false
            }
            Err(e) => {
                error!(
                    "skipping workers for chain {}, client {} & conn {}, reason: {}",
                    chain.id(),
                    client.client_id,
                    connection.connection_id,
                    e
                );

                false
            }
            _ => true,
        }
    }

    fn channel_allowed(&mut self, chain: &Chain, channel: &IdentifiedChannelEnd) -> bool {
        self.config
            .packets_on_channel_allowed(&chain.id(), &channel.port_id, &channel.channel_id)
    }
}

struct ScannedChannel {
    channel: IdentifiedChannelEnd,
    counterparty_channel: Option<IdentifiedChannelEnd>,
    connection: IdentifiedConnectionEnd,
    counterparty_connection_state: Option<ConnectionState>,
    client: IdentifiedAnyClientState,
}

fn scan_allowed_channel<Chain: ChainHandle>(
    registry: &'_ mut Registry<Chain>,
    chain: &Chain,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<ScannedChannel, Error> {
    let span = info_span!("scan.channel", port = %port_id, channel = %channel_id);
    let _guard = span.enter();

    info!("querying channel...");
    let channel = query_channel(chain, port_id, channel_id)?;

    if channel
        .channel_end
        .state_matches(&ChannelState::Uninitialized)
    {
        return Err(Error::uninitialized_channel(
            port_id.clone(),
            channel_id.clone(),
            chain.id(),
        ));
    }

    let connection = query_connection_for_channel(chain, &channel)?;
    let client_id = connection.connection_end.client_id();

    info!(
        connection = %connection.connection_id, client = %client_id,
        "found connection and client",
    );

    info!(client = %client_id, "querying client...");
    let client = query_client(chain, client_id)?;

    info!(
        client = %client_id,
        counterparty_chain = %client.client_state.chain_id(),
        "found counterparty chain for client",
    );

    let counterparty_chain = registry
        .get_or_spawn(&client.client_state.chain_id())
        .map_err(Error::spawn)?;

    let counterparty_channel =
        channel_on_destination(&channel, &connection, &counterparty_chain).unwrap_or_default();

    let counterparty_channel_name = counterparty_channel
        .as_ref()
        .map(|c| c.channel_id.to_string())
        .unwrap_or_else(|| "<none>".to_string());

    info!(
        counterparty_channel = %counterparty_channel_name,
        "found counterparty channel"
    );

    let counterparty_connection_state =
        connection_state_on_destination(&connection, &counterparty_chain)
            .map(Some)
            .unwrap_or_default();

    let counterparty_connection_name = counterparty_connection_state
        .as_ref()
        .map(|s| s.to_string())
        .unwrap_or_else(|| "<none>".to_string());

    info!(
        counterparty_connection_state = %counterparty_connection_name,
        "found counterparty connection state"
    );

    Ok(ScannedChannel {
        channel,
        counterparty_channel,
        connection,
        counterparty_connection_state,
        client,
    })
}

fn query_client<Chain: ChainHandle>(
    chain: &Chain,
    client_id: &ClientId,
) -> Result<IdentifiedAnyClientState, Error> {
    let client = chain
        .query_client_state(client_id, Height::zero())
        .map_err(Error::query)?;

    Ok(IdentifiedAnyClientState::new(client_id.clone(), client))
}

fn query_channel<Chain: ChainHandle>(
    chain: &Chain,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<IdentifiedChannelEnd, Error> {
    let channel_end = chain
        .query_channel(port_id, channel_id, Height::zero())
        .map_err(Error::query)?;

    Ok(IdentifiedChannelEnd::new(
        port_id.clone(),
        channel_id.clone(),
        channel_end,
    ))
}

fn query_connection_for_channel<Chain: ChainHandle>(
    chain: &Chain,
    channel: &IdentifiedChannelEnd,
) -> Result<IdentifiedConnectionEnd, Error> {
    let connection_id = channel
        .channel_end
        .connection_hops()
        .first()
        .cloned()
        .ok_or_else(|| {
            Error::missing_connection_hop(
                channel.port_id.clone(),
                channel.channel_id.clone(),
                chain.id(),
            )
        })?;

    query_connection(chain, &connection_id)
}

fn query_all_clients<Chain: ChainHandle>(
    chain: &Chain,
) -> Result<Vec<IdentifiedAnyClientState>, Error> {
    let clients_req = QueryClientStatesRequest {
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    chain.query_clients(clients_req).map_err(Error::query)
}

fn query_client_connections<Chain: ChainHandle>(
    chain: &Chain,
    client_id: &ClientId,
) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
    let conns_req = QueryClientConnectionsRequest {
        client_id: client_id.to_string(),
    };

    let ids = chain
        .query_client_connections(conns_req)
        .map_err(Error::query)?;

    let connections = ids
        .into_iter()
        .filter_map(|id| match query_connection(chain, &id) {
            Ok(connection) => Some(connection),
            Err(e) => {
                error!("failed to query connection: {}", e);
                None
            }
        })
        .collect_vec();

    Ok(connections)
}

fn query_connection<Chain: ChainHandle>(
    chain: &Chain,
    connection_id: &ConnectionId,
) -> Result<IdentifiedConnectionEnd, Error> {
    let connection_end = chain
        .query_connection(connection_id, Height::zero())
        .map_err(Error::query)?;

    Ok(IdentifiedConnectionEnd {
        connection_id: connection_id.clone(),
        connection_end,
    })
}

fn query_connection_channels<Chain: ChainHandle>(
    chain: &Chain,
    connection_id: &ConnectionId,
) -> Result<Vec<IdentifiedChannelEnd>, Error> {
    let chans_req = QueryConnectionChannelsRequest {
        connection: connection_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    chain
        .query_connection_channels(chans_req)
        .map_err(Error::query)
}
