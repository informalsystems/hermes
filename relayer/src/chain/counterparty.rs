use serde::{Deserialize, Serialize};
use tracing::trace;

use ibc::{
    ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
    ics03_connection::connection::IdentifiedConnectionEnd,
    ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd, State},
    ics24_host::identifier::ConnectionId,
    ics24_host::identifier::{ChainId, ChannelId, PortId},
    Height,
};
use ibc_proto::ibc::core::channel::v1::QueryConnectionChannelsRequest;

use crate::supervisor::Error;

use super::handle::ChainHandle;

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
    trace!(
        chain_id = %chain.id(),
        port_id = %port_id,
        channel_id = %channel_id,
        "getting counterparty chain"
    );

    let channel_end = chain
        .query_channel(port_id, channel_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    if channel_end.state_matches(&State::Uninitialized) {
        return Err(Error::ChannelUninitialized(channel_id.clone(), chain.id()));
    }

    let connection_id = channel_end
        .connection_hops()
        .first()
        .ok_or_else(|| Error::MissingConnectionHops(channel_id.clone(), chain.id()))?;

    let connection_end = chain
        .query_connection(&connection_id)
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
        .query_client_state(&client_id, Height::zero())
        .map_err(|e| Error::QueryFailed(format!("{}", e)))?;

    trace!(
        chain_id=%chain.id(), port_id=%port_id, channel_id=%channel_id,
        "counterparty chain: {}", client_state.chain_id()
    );

    let client = IdentifiedAnyClientState::new(client_id.clone(), client_state);
    let connection = IdentifiedConnectionEnd::new(connection_id.clone(), connection_end);
    let channel = IdentifiedChannelEnd::new(port_id.clone(), channel_id.clone(), channel_end);

    Ok(ChannelConnectionClient::new(channel, connection, client))
}

pub fn get_counterparty_chain(
    src_chain: &dyn ChainHandle,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
) -> Result<ChainId, Error> {
    channel_connection_client(src_chain, src_port_id, src_channel_id)
        .map(|c| c.client.client_state.chain_id())
}

fn channel_on_destination(
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
    channel: IdentifiedChannelEnd,
    connection: IdentifiedConnectionEnd,
    counterparty_chain: &dyn ChainHandle,
) -> Result<State, Error> {
    let counterparty_state =
        if let Some(remote_channel_id) = channel.channel_end.remote.channel_id() {
            counterparty_chain
                .query_channel(
                    channel.channel_end.remote.port_id(),
                    remote_channel_id,
                    Height::zero(),
                )
                .map_err(|e| Error::QueryFailed(format!("{}", e)))?
                .state
        } else if let Some(remote_connection_id) = connection.end().counterparty().connection_id() {
            channel_on_destination(
                &channel.port_id,
                &channel.channel_id,
                counterparty_chain,
                remote_connection_id,
            )?
            .map_or_else(
                || State::Uninitialized,
                |remote_channel| remote_channel.state,
            )
        } else {
            State::Uninitialized
        };
    Ok(counterparty_state)
}
