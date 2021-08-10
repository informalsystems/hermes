use tracing::{error, trace};

use ibc::tagged::Tagged;
use ibc::{
    ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::channel::State,
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortChannelId, PortId},
    Height,
};
use ibc_proto::ibc::core::{
    channel::v1::QueryConnectionChannelsRequest, connection::v1::QueryClientConnectionsRequest,
};

use crate::channel::{ChannelEnd, ChannelError, IdentifiedChannelEnd};
use crate::connection::{ConnectionEnd, IdentifiedConnectionEnd};
use crate::supervisor::Error;

use super::handle::ChainHandle;

pub fn counterparty_chain_from_connection<Chain, Counterparty>(
    src_chain: &Chain,
    src_connection_id: Tagged<Chain, ConnectionId>,
) -> Result<Tagged<Counterparty, ChainId>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let connection_end = src_chain
        .query_connection(src_connection_id, Height::tagged_zero())
        .map_err(Error::relayer)?;

    let client_id = connection_end.client_id();
    let client_state = src_chain
        .query_client_state(client_id, Height::tagged_zero())
        .map_err(Error::relayer)?;

    trace!(
        chain_id=%src_chain.id(), connection_id=%src_connection_id,
        "counterparty chain: {}", client_state.chain_id()
    );
    Ok(client_state.chain_id())
}

fn connection_on_destination<Chain, Counterparty>(
    connection_id_on_source: Tagged<Counterparty, ConnectionId>,
    counterparty_client_id: Tagged<Chain, ClientId>,
    counterparty_chain: &Chain,
) -> Result<Option<ConnectionEnd<Chain, Counterparty>>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let req = QueryClientConnectionsRequest {
        client_id: counterparty_client_id.to_string(),
    };

    let counterparty_connections = counterparty_chain
        .query_client_connections(req)
        .map_err(Error::relayer)?;

    for counterparty_connection in counterparty_connections.into_iter() {
        let counterparty_connection_end = counterparty_chain
            .query_connection(counterparty_connection, Height::tagged_zero())
            .map_err(Error::relayer)?;

        let local_connection_end = counterparty_connection_end.counterparty();

        let local_connection_end_id = local_connection_end.connection_id();

        if let Some(local_connection_id) = local_connection_end_id {
            if local_connection_id == connection_id_on_source {
                return Ok(Some(counterparty_connection_end));
            }
        }
    }
    Ok(None)
}

pub fn connection_state_on_destination<Chain, Counterparty>(
    connection: IdentifiedConnectionEnd<Counterparty, Chain>,
    counterparty_chain: &Chain,
) -> Result<Tagged<Chain, ConnectionState>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let remote_connection = connection.counterparty();
    let m_remote_connection_id = remote_connection.connection_id();

    if let Some(remote_connection_id) = m_remote_connection_id {
        let connection_end = counterparty_chain
            .query_connection(remote_connection_id, Height::tagged_zero())
            .map_err(Error::relayer)?;

        Ok(connection_end.state())
    } else {
        // The remote connection id (used on `counterparty_chain`) is unknown.
        // Try to retrieve this id by looking at client connections.
        let counterparty_client_id = remote_connection.client_id();

        let dst_connection = connection_on_destination(
            connection.connection_id(),
            counterparty_client_id,
            counterparty_chain,
        )?;

        match dst_connection {
            Some(remote_connection) => Ok(remote_connection.state()),
            None => Ok(Tagged::new(ConnectionState::Uninitialized)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ChannelConnectionClient<Chain, Counterparty> {
    pub channel: IdentifiedChannelEnd<Chain, Counterparty>,
    pub connection: IdentifiedConnectionEnd<Chain, Counterparty>,
    pub client: IdentifiedAnyClientState,
}

impl<Chain, Counterparty> ChannelConnectionClient<Chain, Counterparty> {
    pub fn new(
        channel: IdentifiedChannelEnd<Chain, Counterparty>,
        connection: IdentifiedConnectionEnd<Chain, Counterparty>,
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
pub fn channel_connection_client<Chain, Counterparty>(
    chain: &Chain,
    port_id: Tagged<Chain, PortId>,
    channel_id: Tagged<Chain, ChannelId>,
) -> Result<ChannelConnectionClient<Chain, Counterparty>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let channel_end = chain
        .query_channel(port_id, channel_id, Height::tagged_zero())
        .map_err(Error::relayer)?;

    if channel_end.0.value().state_matches(&State::Uninitialized) {
        return Err(Error::channel_uninitialized(
            port_id.untag(),
            channel_id.untag(),
            chain.id().untag(),
        ));
    }

    let connection_id = channel_end
        .connection_hops()
        .first()
        .map(Clone::clone)
        .ok_or_else(|| {
            Error::missing_connection_hops(channel_id.value().clone(), chain.id().value().clone())
        })?;

    let connection_end = chain
        .query_connection(connection_id, Height::tagged_zero())
        .map_err(Error::relayer)?;

    if !connection_end.0.value().is_open() {
        return Err(Error::connection_not_open(
            connection_id.untag(),
            channel_id.untag(),
            chain.id().untag(),
        ));
    }

    let client_id = connection_end.client_id();

    let client_state = chain
        .query_client_state(client_id, Height::tagged_zero())
        .map_err(Error::relayer)?;

    let client = IdentifiedAnyClientState::new(client_id.untag(), client_state.0.untag());

    let connection = IdentifiedConnectionEnd::new(connection_id, connection_end);

    let channel = IdentifiedChannelEnd::new(port_id, channel_id, channel_end);

    Ok(ChannelConnectionClient::new(channel, connection, client))
}

pub fn counterparty_chain_from_channel<Chain, Counterparty>(
    src_chain: &Chain,
    src_channel_id: Tagged<Chain, ChannelId>,
    src_port_id: Tagged<Chain, PortId>,
) -> Result<ChainId, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let client = channel_connection_client(src_chain, src_port_id, src_channel_id)?;
    Ok(client.client.client_state.chain_id())
}

fn fetch_channel_on_destination<Chain, Counterparty>(
    port_id: Tagged<Counterparty, PortId>,
    channel_id: Tagged<Counterparty, ChannelId>,
    counterparty_chain: &Chain,
    remote_connection_id: Tagged<Chain, ConnectionId>,
) -> Result<Option<ChannelEnd<Chain, Counterparty>>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let req = QueryConnectionChannelsRequest {
        connection: remote_connection_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let counterparty_channels = counterparty_chain
        .query_connection_channels(req)
        .map_err(Error::relayer)?;

    for counterparty_channel in counterparty_channels.into_iter() {
        let local_channel_end = counterparty_channel.counterparty();

        let m_local_channel_id = local_channel_end.channel_id();

        let local_channel_end_port_id = local_channel_end.port_id();

        if let Some(local_channel_id) = m_local_channel_id {
            if local_channel_id == channel_id && local_channel_end_port_id == port_id {
                return Ok(Some(counterparty_channel.channel_end()));
            }
        }
    }

    Ok(None)
}

pub fn channel_state_on_destination<Chain, Counterparty>(
    channel: IdentifiedChannelEnd<Counterparty, Chain>,
    connection: IdentifiedConnectionEnd<Counterparty, Chain>,
    counterparty_chain: &Chain,
) -> Result<Tagged<Chain, State>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let remote_channel = channel_on_destination(channel, connection, counterparty_chain)?;

    let state = remote_channel
        .map(|c| c.state())
        .unwrap_or(Tagged::new(State::Uninitialized));

    Ok(state)
}

pub fn channel_on_destination<Chain, Counterparty>(
    channel: IdentifiedChannelEnd<Counterparty, Chain>,
    connection: IdentifiedConnectionEnd<Counterparty, Chain>,
    counterparty_chain: &Chain,
) -> Result<Option<ChannelEnd<Chain, Counterparty>>, Error>
where
    Chain: ChainHandle<Counterparty>,
{
    let remote_channel = channel.counterparty();

    let remote_connection = connection.counterparty();

    let m_remote_channel_id = remote_channel.channel_id();

    let m_remote_connection_id = remote_connection.connection_id();

    if let Some(remote_channel_id) = m_remote_channel_id {
        let remote_channel_port_id = remote_channel.port_id();

        let counterparty = counterparty_chain
            .query_channel(
                remote_channel_port_id,
                remote_channel_id,
                Height::tagged_zero(),
            )
            .map_err(Error::relayer)?;

        Ok(Some(counterparty))
    } else {
        if let Some(remote_connection_id) = m_remote_connection_id {
            fetch_channel_on_destination(
                channel.port_id(),
                channel.channel_id(),
                counterparty_chain,
                remote_connection_id,
            )
        } else {
            Ok(None)
        }
    }
}

/// Queries a channel end on a [`ChainHandle`], and verifies
/// that the counterparty field on that channel end matches an
/// expected counterparty.
/// Returns `Ok` if the counterparty matches, and `Err` otherwise.
pub fn check_channel_counterparty<Chain, Counterparty>(
    target_chain: &Chain,
    target_pchan: Tagged<Chain, PortChannelId>,
    expected: Tagged<Counterparty, PortChannelId>,
) -> Result<(), ChannelError>
where
    Chain: ChainHandle<Counterparty>,
{
    let channel_end_dst = target_chain
        .query_channel(
            target_pchan.map(|c| c.port_id.clone()),
            target_pchan.map(|c| c.channel_id.clone()),
            Height::tagged_zero(),
        )
        .map_err(|e| ChannelError::query(target_chain.id().value().clone(), e))?;

    let counterparty = channel_end_dst.counterparty();
    let m_actual_port_channel_id = counterparty
        .0
        .map(|c| {
            c.channel_id.map(|channel_id| PortChannelId {
                channel_id,
                port_id: c.port_id.clone(),
            })
        })
        .transpose();

    match m_actual_port_channel_id {
        Some(actual_port_channel_id) => {
            if actual_port_channel_id != expected {
                return Err(ChannelError::mismatch_channel_ends(
                    target_chain.id().untag(),
                    target_pchan.untag(),
                    expected.untag(),
                    actual_port_channel_id.untag(),
                ));
            }
        }
        None => {
            error!(
                "channel {} on chain {} has no counterparty channel id ",
                target_pchan,
                target_chain.id()
            );
            return Err(ChannelError::incomplete_channel_state(
                target_chain.id().untag(),
                target_pchan.untag(),
            ));
        }
    }

    Ok(())
}
