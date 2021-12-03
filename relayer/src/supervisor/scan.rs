#![allow(unused_imports)]

use core::fmt;
use std::collections::BTreeMap;

use itertools::Itertools;
use tracing::{debug, error, info_span, warn};

use ibc::{
    core::{
        ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
        ics03_connection::connection::{IdentifiedConnectionEnd, State as ConnectionState},
        ics04_channel::channel::{IdentifiedChannelEnd, State as ChannelState},
        ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId},
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
    config::{ChainConfig, Config, ModeConfig, PacketFilter},
    object::{Channel, Client, Connection, Object, Packet},
    registry::SharedRegistry,
    supervisor::client_state_filter::{FilterPolicy, Permission},
    supervisor::error::Error as SupervisorError,
    worker::WorkerMap,
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
    }
}

#[derive(Debug)]
pub struct ChainsScan {
    pub chains: Vec<Result<ChainScan, Error>>,
}

impl ChainsScan {}

impl fmt::Display for ChainsScan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for scan in self.chains.iter().flatten() {
            writeln!(f, "# Chain:{}", scan.chain_id)?;

            for client in &scan.clients {
                writeln!(f, "  - Client: {}", client.client.client_id)?;

                for conn in &client.connections {
                    let counterparty = conn.counterparty_state();
                    writeln!(f, "    * Connection: {}", conn.connection.connection_id)?;
                    writeln!(f, "      | State: {}", conn.state())?;
                    writeln!(f, "      | Counterparty state: {}", counterparty)?;

                    for chan in &conn.channels {
                        let counterparty = chan
                            .counterparty
                            .as_ref()
                            .map(|c| c.channel_id.to_string())
                            .unwrap_or_else(|| "<none>".to_string());

                        writeln!(f, "      + Channel: {}", chan.channel.channel_id)?;
                        writeln!(f, "        | Port: {}", chan.channel.port_id)?;
                        writeln!(f, "        | State: {}", chan.channel.channel_end.state())?;
                        writeln!(f, "        | Counterparty state: {}", counterparty)?;
                    }
                }
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct ChainScan {
    pub chain_id: ChainId,
    pub clients: Vec<ClientScan>,
}

#[derive(Debug)]
pub struct ClientScan {
    pub client: IdentifiedAnyClientState,
    pub connections: Vec<ConnectionScan>,
}

#[derive(Debug)]
pub struct ConnectionScan {
    pub connection: IdentifiedConnectionEnd,
    pub counterparty_state: ConnectionState,
    pub channels: Vec<ChannelScan>,
}

impl ConnectionScan {
    pub fn state(&self) -> ConnectionState {
        self.connection.connection_end.state
    }
    pub fn counterparty_state(&self) -> ConnectionState {
        self.counterparty_state
    }
}

#[derive(Debug)]
pub struct ChannelScan {
    pub channel: IdentifiedChannelEnd,
    pub counterparty: Option<IdentifiedChannelEnd>,
}

impl ChannelScan {
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

pub struct ChainScanner<'a, Chain: ChainHandle> {
    config: Config,
    registry: SharedRegistry<Chain>,
    client_state_filter: &'a mut FilterPolicy,
}

impl<'a, Chain: ChainHandle> ChainScanner<'a, Chain> {
    pub fn new(
        config: Config,
        registry: SharedRegistry<Chain>,
        client_state_filter: &'a mut FilterPolicy,
    ) -> Self {
        Self {
            config,
            registry,
            client_state_filter,
        }
    }

    pub fn scan_chains(&mut self) -> ChainsScan {
        let mut scans = ChainsScan {
            chains: Vec::with_capacity(self.config.chains.len()),
        };

        for chain in self.config.chains.clone() {
            scans.chains.push(self.scan_chain(&chain));
        }

        scans
    }

    pub fn scan_chain(&mut self, chain_config: &ChainConfig) -> Result<ChainScan, Error> {
        let span = info_span!("scan.chain", chain_id = %chain_config.id, );
        let _guard = span.enter();

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

        let mut scan = ChainScan {
            chain_id: chain_config.id.clone(),
            clients: Vec::new(),
        };

        self.scan_all_clients(&chain, &mut scan)?;

        Ok(scan)
    }

    pub fn scan_all_clients(&mut self, chain: &Chain, scan: &mut ChainScan) -> Result<(), Error> {
        let clients = query_all_clients(chain)?;

        for client in clients {
            if let Some(client_scan) = self.scan_client(chain, client)? {
                scan.clients.push(client_scan);
            }
        }

        Ok(())
    }

    fn scan_client(
        &mut self,
        chain: &Chain,
        client: IdentifiedAnyClientState,
    ) -> Result<Option<ClientScan>, Error> {
        let span = info_span!("scan.client", client_id = %client.client_id);
        let _guard = span.enter();

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
                chain_id = %chain.id(),
                counterparty_chain_id = %counterparty_chain_id,
                "skipping client because its counterparty is not present in the config",
            );

            return Ok(None);
        }

        let client_connections_ids = query_client_connections(chain, &client.client_id)?;

        let mut scan = ClientScan {
            client,
            connections: Vec::new(),
        };

        for connection_id in client_connections_ids {
            if let Some(connection_scan) =
                self.scan_connection(chain, &scan.client, connection_id)?
            {
                scan.connections.push(connection_scan);
            }
        }

        Ok(Some(scan))
    }

    fn scan_connection(
        &mut self,
        chain: &Chain,
        client: &IdentifiedAnyClientState,
        connection_end: IdentifiedConnectionEnd,
    ) -> Result<Option<ConnectionScan>, Error> {
        let span = info_span!("scan.connection", connection = %connection_end.connection_id);
        let _guard = span.enter();

        if !self.connection_allowed(chain, client, &connection_end) {
            warn!("skipping connection, reason: connection is not allowed",);
            return Ok(None);
        }

        let connection = &connection_end.connection_end;
        let connection_id = &connection_end.connection_id;

        if !connection.is_open() {
            debug!("connection is not open, skipping scan of channels over this connection");
            return Ok(None);
        }

        let counterparty_state = match self.counterparty_connection_state(client, &connection_end) {
            Err(e) => {
                error!("error fetching counterparty connection state: {}", e);
                return Ok(None);
            }
            Ok(state) if !state.eq(&ConnectionState::Open) => {
                warn!("counterparty connection is not open, skipping scan of channels over this connection");
                return Ok(None);
            }
            Ok(state) => state,
        };

        let channels = match query_connection_channels(chain, connection_id) {
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
                    channel_on_destination(&channel, &connection_end, &counterparty_chain)
                        .unwrap_or_default();

                ChannelScan {
                    channel,
                    counterparty,
                }
            })
            .collect();

        Ok(Some(ConnectionScan {
            connection: connection_end,
            counterparty_state,
            channels,
        }))
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

        // FIXME
        Ok(connection_state_on_destination(connection, &counterparty_chain).unwrap())
    }

    fn client_filter_enabled(&self) -> bool {
        self.config.mode.packets.filter
    }

    fn client_allowed(&mut self, chain: &Chain, client: &IdentifiedAnyClientState) -> bool {
        if !self.client_filter_enabled() {
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
        if !self.client_filter_enabled() {
            return true;
        }

        let permission = self.client_state_filter.control_connection_end_and_client(
            &mut self.registry.write(),
            &chain.id(),
            &client.client_state,
            &connection.connection_end,
            &connection.connection_id,
        );

        match permission {
            Ok(Permission::Deny) => {
                warn!(
                    "skipping workers for chain {}, client {} & conn {}. \
                                 reason: client or counterparty client is not allowed",
                    chain.id(),
                    client.client_id,
                    connection.connection_id
                );

                false
            }
            Err(e) => {
                error!(
                    "skipping workers for chain {}, client {} & conn {}. reason: {}",
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

// fn query_clients_for_channels<C: ChainHandle>(
//     _chain: &C,
//     _channels: Vec<ChannelId>,
// ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
//     todo!()
// }

// fn query_client_for_channel<C: ChainHandle>(
//     _chain: &C,
//     _channel: ChannelId,
// ) -> Result<IdentifiedAnyClientState, Error> {
//     todo!()
// }

// fn query_channel<C: ChainHandle>(
//     _chain: &C,
//     _channel_id: ChannelId,
// ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
//     todo!()
// }

// fn query_connection_for_channel<C: ChainHandle>(
//     _chain: &C,
//     _channel: IdentifiedChannelEnd,
// ) -> Result<IdentifiedConnectionEnd, Error> {
//     todo!()
// }

fn query_all_clients<C: ChainHandle>(chain: &C) -> Result<Vec<IdentifiedAnyClientState>, Error> {
    let clients_req = QueryClientStatesRequest {
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    chain.query_clients(clients_req).map_err(Error::query)
}

fn query_client_connections<C: ChainHandle>(
    chain: &C,
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
        .filter_map(|id| match query_connection(chain, id) {
            Ok(connection) => Some(connection),
            Err(e) => {
                error!("failed to query connection: {}", e);
                None
            }
        })
        .collect_vec();

    Ok(connections)
}

fn query_connection<C: ChainHandle>(
    chain: &C,
    connection_id: ConnectionId,
) -> Result<IdentifiedConnectionEnd, Error> {
    let connection_end = chain
        .query_connection(&connection_id, Height::zero())
        .map_err(Error::query)?;

    Ok(IdentifiedConnectionEnd {
        connection_id,
        connection_end,
    })
}

fn query_connection_channels<C: ChainHandle>(
    chain: &C,
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
