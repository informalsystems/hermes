use serde::{Deserialize, Serialize};
use tracing::{error, trace};

use ibc::{
    ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
    ics03_connection::connection::{
        ConnectionEnd, IdentifiedConnectionEnd, State as ConnectionState,
    },
    ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd, State},
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortChannelId, PortId},
    Height,
};
use ibc_proto::ibc::core::{
    channel::v1::QueryConnectionChannelsRequest, connection::v1::QueryClientConnectionsRequest,
};

use crate::channel::ChannelError;
use crate::supervisor::Error;

use super::handle::ChainHandle;

pub fn counterparty_chain_from_connection(
    src_chain: &dyn ChainHandle,
    src_connection_id: &ConnectionId,
) -> Result<ChainId, Error> {
    let connection_end = src_chain
        .query_connection(&src_connection_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    let client_id = connection_end.client_id();
    let client_state = src_chain
        .query_client_state(&client_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    trace!(
        chain_id=%src_chain.id(), connection_id=%src_connection_id,
        "counterparty chain: {}", client_state.chain_id()
    );
    Ok(client_state.chain_id())
}

fn connection_on_destination(
    connection_id_on_source: &ConnectionId,
    counterparty_client_id: &ClientId,
    counterparty_chain: &dyn ChainHandle,
) -> Result<Option<ConnectionEnd>, Error> {
    let req = QueryClientConnectionsRequest {
        client_id: counterparty_client_id.to_string(),
    };

    let counterparty_connections =
        counterparty_chain
            .query_client_connections(req)
            .map_err(|e| {
                Error::QueryFailed(format!(
                    "counterparty::query_client_connections({}) failed with error: {}",
                    counterparty_client_id, e
                ))
            })?;

    for counterparty_connection in counterparty_connections.into_iter() {
        let counterparty_connection_end = counterparty_chain
            .query_connection(&counterparty_connection, Height::zero())
            .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

        let local_connection_end = &counterparty_connection_end.counterparty();
        if let Some(local_connection_id) = local_connection_end.connection_id() {
            if local_connection_id == connection_id_on_source {
                return Ok(Some(counterparty_connection_end));
            }
        }
    }
    Ok(None)
}

pub fn connection_state_on_destination(
    connection: IdentifiedConnectionEnd,
    counterparty_chain: &dyn ChainHandle,
) -> Result<ConnectionState, Error> {
    if let Some(remote_connection_id) = connection.connection_end.counterparty().connection_id() {
        let connection_end = counterparty_chain
            .query_connection(remote_connection_id, Height::zero())
            .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

        Ok(connection_end.state)
    } else {
        // The remote connection id (used on `counterparty_chain`) is unknown.
        // Try to retrieve this id by looking at client connections.
        let counterparty_client_id = connection.connection_end.counterparty().client_id();

        let dst_connection = connection_on_destination(
            &connection.connection_id,
            counterparty_client_id,
            counterparty_chain,
        )?;

        dst_connection.map_or_else(
            || Ok(ConnectionState::Uninitialized),
            |remote_connection| Ok(remote_connection.state),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChannelConnectionClient {
    pub channel: IdentifiedChannelEnd,
    pub connection: IdentifiedConnectionEnd,
    pub client: IdentifiedAnyClientState,
}

impl ChannelConnectionClient {
    pub fn new(
        channel: IdentifiedChannelEnd,
        connection: IdentifiedConnectionEnd,
        client: IdentifiedAnyClientState,
    ) -> Self {
        Self {
            channel,
            connection,
            client,
        }
    }
}

/// Returns the [`ChannelConnectionClient`] associated with the
/// provided port and channel id.
pub fn channel_connection_client(
    chain: &dyn ChainHandle,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<ChannelConnectionClient, Error> {
    let channel_end = chain
        .query_channel(port_id, channel_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    if channel_end.state_matches(&State::Uninitialized) {
        return Err(Error::ChannelUninitialized(
            port_id.clone(),
            channel_id.clone(),
            chain.id(),
        ));
    }

    let connection_id = channel_end
        .connection_hops()
        .first()
        .ok_or_else(|| Error::MissingConnectionHops(channel_id.clone(), chain.id()))?;

    let connection_end = chain
        .query_connection(connection_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    if !connection_end.is_open() {
        return Err(Error::ConnectionNotOpen(
            connection_id.clone(),
            channel_id.clone(),
            chain.id(),
        ));
    }

    let client_id = connection_end.client_id();
    let client_state = chain
        .query_client_state(client_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    let client = IdentifiedAnyClientState::new(client_id.clone(), client_state);
    let connection = IdentifiedConnectionEnd::new(connection_id.clone(), connection_end);
    let channel = IdentifiedChannelEnd::new(port_id.clone(), channel_id.clone(), channel_end);

    Ok(ChannelConnectionClient::new(channel, connection, client))
}

pub fn counterparty_chain_from_channel(
    src_chain: &dyn ChainHandle,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
) -> Result<ChainId, Error> {
    channel_connection_client(src_chain, src_port_id, src_channel_id)
        .map(|c| c.client.client_state.chain_id())
}

fn fetch_channel_on_destination(
    port_id: &PortId,
    channel_id: &ChannelId,
    counterparty_chain: &dyn ChainHandle,
    remote_connection_id: &ConnectionId,
) -> Result<Option<ChannelEnd>, Error> {
    let req = QueryConnectionChannelsRequest {
        connection: remote_connection_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let counterparty_channels = counterparty_chain
        .query_connection_channels(req)
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    for counterparty_channel in counterparty_channels.into_iter() {
        let local_channel_end = &counterparty_channel.channel_end.remote;
        if let Some(local_channel_id) = local_channel_end.channel_id() {
            if local_channel_id == channel_id && local_channel_end.port_id() == port_id {
                return Ok(Some(counterparty_channel.channel_end));
            }
        }
    }
    Ok(None)
}

pub fn channel_state_on_destination(
    channel: &IdentifiedChannelEnd,
    connection: &IdentifiedConnectionEnd,
    counterparty_chain: &dyn ChainHandle,
) -> Result<State, Error> {
    let remote_channel = channel_on_destination(channel, connection, counterparty_chain)?;
    Ok(remote_channel.map_or_else(
        || State::Uninitialized,
        |remote_channel| remote_channel.state,
    ))
}

pub fn channel_on_destination(
    channel: &IdentifiedChannelEnd,
    connection: &IdentifiedConnectionEnd,
    counterparty_chain: &dyn ChainHandle,
) -> Result<Option<ChannelEnd>, Error> {
    if let Some(remote_channel_id) = channel.channel_end.remote.channel_id() {
        let counterparty = counterparty_chain
            .query_channel(
                channel.channel_end.remote.port_id(),
                remote_channel_id,
                Height::zero(),
            )
            .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

        Ok(Some(counterparty))
    } else if let Some(remote_connection_id) = connection.end().counterparty().connection_id() {
        fetch_channel_on_destination(
            &channel.port_id,
            &channel.channel_id,
            counterparty_chain,
            remote_connection_id,
        )
    } else {
        Ok(None)
    }
}

/// Queries a channel end on a [`ChainHandle`], and verifies
/// that the counterparty field on that channel end matches an
/// expected counterparty.
/// Returns `Ok` if the counterparty matches, and `Err` otherwise.
pub fn check_channel_counterparty(
    target_chain: Box<dyn ChainHandle>,
    target_pchan: &PortChannelId,
    expected: &PortChannelId,
) -> Result<(), ChannelError> {
    let channel_end_dst = target_chain
        .query_channel(
            &target_pchan.port_id,
            &target_pchan.channel_id,
            Height::zero(),
        )
        .map_err(|e| ChannelError::QueryError(target_chain.id(), e))?;

    let counterparty = channel_end_dst.remote;
    match counterparty.channel_id {
        Some(actual_channel_id) => {
            let actual = PortChannelId {
                channel_id: actual_channel_id,
                port_id: counterparty.port_id,
            };
            if &actual != expected {
                return Err(ChannelError::MismatchingChannelEnds(
                    target_pchan.clone(),
                    target_chain.id(),
                    expected.clone(),
                    actual,
                ));
            }
        }
        None => {
            error!(
                "channel {} on chain {} has no counterparty channel id ",
                target_pchan,
                target_chain.id()
            );
            return Err(ChannelError::IncompleteChannelState(
                target_pchan.clone(),
                target_chain.id(),
            ));
        }
    }

    Ok(())
}
