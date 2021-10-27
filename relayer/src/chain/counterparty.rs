use serde::{Deserialize, Serialize};
use tracing::{error, trace};

use crate::channel::ChannelError;
use crate::supervisor::Error;
use ibc::{
    core::{
        ics02_client::client_state::{ClientState, IdentifiedAnyClientState},
        ics03_connection::connection::{
            ConnectionEnd, IdentifiedConnectionEnd, State as ConnectionState,
        },
        ics04_channel::channel::{IdentifiedChannelEnd, State},
        ics24_host::identifier::{
            ChainId, ChannelId, ClientId, ConnectionId, PortChannelId, PortId,
        },
    },
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    QueryConnectionChannelsRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::connection::v1::QueryClientConnectionsRequest;

use super::handle::ChainHandle;

pub fn counterparty_chain_from_connection(
    src_chain: &impl ChainHandle,
    src_connection_id: &ConnectionId,
) -> Result<ChainId, Error> {
    let connection_end = src_chain
        .query_connection(src_connection_id, Height::zero())
        .map_err(Error::relayer)?;

    let client_id = connection_end.client_id();
    let client_state = src_chain
        .query_client_state(client_id, Height::zero())
        .map_err(Error::relayer)?;

    trace!(
        chain_id=%src_chain.id(), connection_id=%src_connection_id,
        "counterparty chain: {}", client_state.chain_id()
    );
    Ok(client_state.chain_id())
}

fn connection_on_destination(
    connection_id_on_source: &ConnectionId,
    counterparty_client_id: &ClientId,
    counterparty_chain: &impl ChainHandle,
) -> Result<Option<ConnectionEnd>, Error> {
    let req = QueryClientConnectionsRequest {
        client_id: counterparty_client_id.to_string(),
    };

    let counterparty_connections = counterparty_chain
        .query_client_connections(req)
        .map_err(Error::relayer)?;

    for counterparty_connection in counterparty_connections.into_iter() {
        let counterparty_connection_end = counterparty_chain
            .query_connection(&counterparty_connection, Height::zero())
            .map_err(Error::relayer)?;

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
    counterparty_chain: &impl ChainHandle,
) -> Result<ConnectionState, Error> {
    if let Some(remote_connection_id) = connection.connection_end.counterparty().connection_id() {
        let connection_end = counterparty_chain
            .query_connection(remote_connection_id, Height::zero())
            .map_err(Error::relayer)?;

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
    chain: &impl ChainHandle,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<ChannelConnectionClient, Error> {
    let channel_end = chain
        .query_channel(port_id, channel_id, Height::zero())
        .map_err(Error::relayer)?;

    if channel_end.state_matches(&State::Uninitialized) {
        return Err(Error::channel_uninitialized(
            port_id.clone(),
            channel_id.clone(),
            chain.id(),
        ));
    }

    let connection_id = channel_end
        .connection_hops()
        .first()
        .ok_or_else(|| Error::missing_connection_hops(channel_id.clone(), chain.id()))?;

    let connection_end = chain
        .query_connection(connection_id, Height::zero())
        .map_err(Error::relayer)?;

    if !connection_end.is_open() {
        return Err(Error::connection_not_open(
            connection_id.clone(),
            channel_id.clone(),
            chain.id(),
        ));
    }

    let client_id = connection_end.client_id();
    let client_state = chain
        .query_client_state(client_id, Height::zero())
        .map_err(Error::relayer)?;

    let client = IdentifiedAnyClientState::new(client_id.clone(), client_state);
    let connection = IdentifiedConnectionEnd::new(connection_id.clone(), connection_end);
    let channel = IdentifiedChannelEnd::new(port_id.clone(), channel_id.clone(), channel_end);

    Ok(ChannelConnectionClient::new(channel, connection, client))
}

pub fn counterparty_chain_from_channel(
    src_chain: &impl ChainHandle,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
) -> Result<ChainId, Error> {
    channel_connection_client(src_chain, src_port_id, src_channel_id)
        .map(|c| c.client.client_state.chain_id())
}

fn fetch_channel_on_destination(
    port_id: &PortId,
    channel_id: &ChannelId,
    counterparty_chain: &impl ChainHandle,
    remote_connection_id: &ConnectionId,
) -> Result<Option<IdentifiedChannelEnd>, Error> {
    let req = QueryConnectionChannelsRequest {
        connection: remote_connection_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let counterparty_channels = counterparty_chain
        .query_connection_channels(req)
        .map_err(Error::relayer)?;

    for counterparty_channel in counterparty_channels.into_iter() {
        let local_channel_end = &counterparty_channel.channel_end.remote;
        if let Some(local_channel_id) = local_channel_end.channel_id() {
            if local_channel_id == channel_id && local_channel_end.port_id() == port_id {
                return Ok(Some(counterparty_channel));
            }
        }
    }
    Ok(None)
}

pub fn channel_state_on_destination(
    channel: &IdentifiedChannelEnd,
    connection: &IdentifiedConnectionEnd,
    counterparty_chain: &impl ChainHandle,
) -> Result<State, Error> {
    let remote_channel = channel_on_destination(channel, connection, counterparty_chain)?;
    Ok(remote_channel.map_or_else(
        || State::Uninitialized,
        |remote_channel| remote_channel.channel_end.state,
    ))
}

pub fn channel_on_destination(
    channel: &IdentifiedChannelEnd,
    connection: &IdentifiedConnectionEnd,
    counterparty_chain: &impl ChainHandle,
) -> Result<Option<IdentifiedChannelEnd>, Error> {
    if let Some(remote_channel_id) = channel.channel_end.counterparty().channel_id() {
        let counterparty = counterparty_chain
            .query_channel(
                channel.channel_end.counterparty().port_id(),
                remote_channel_id,
                Height::zero(),
            )
            .map(|c| IdentifiedChannelEnd {
                port_id: channel.channel_end.counterparty().port_id().clone(),
                channel_id: remote_channel_id.clone(),
                channel_end: c,
            })
            .map_err(Error::relayer)?;

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
    target_chain: impl ChainHandle,
    target_pchan: &PortChannelId,
    expected: &PortChannelId,
) -> Result<(), ChannelError> {
    let channel_end_dst = target_chain
        .query_channel(
            &target_pchan.port_id,
            &target_pchan.channel_id,
            Height::zero(),
        )
        .map_err(|e| ChannelError::query(target_chain.id(), e))?;

    let counterparty = channel_end_dst.remote;
    match counterparty.channel_id {
        Some(actual_channel_id) => {
            let actual = PortChannelId {
                channel_id: actual_channel_id,
                port_id: counterparty.port_id,
            };
            if &actual != expected {
                return Err(ChannelError::mismatch_channel_ends(
                    target_chain.id(),
                    target_pchan.clone(),
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
            return Err(ChannelError::incomplete_channel_state(
                target_chain.id(),
                target_pchan.clone(),
            ));
        }
    }

    Ok(())
}

pub fn unreceived_packets(
    chain: &impl ChainHandle,
    counterparty_chain: &impl ChainHandle,
    channel: IdentifiedChannelEnd,
) -> Result<Vec<u64>, Error> {
    let counterparty_channel_id = channel
        .channel_end
        .counterparty()
        .channel_id
        .as_ref()
        .ok_or_else(Error::missing_counterparty_channel_id)?;

    let (_, sequences, _) = unreceived_packets_sequences(
        counterparty_chain,
        counterparty_channel_id,
        &channel.channel_end.counterparty().port_id,
        chain,
        &channel.channel_id,
        &channel.port_id,
    )?;

    Ok(sequences)
}

pub(crate) fn unreceived_packets_sequences(
    src_chain: &impl ChainHandle,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
    dst_chain: &impl ChainHandle,
    dst_channel_id: &ChannelId,
    dst_port_id: &PortId,
) -> Result<(Vec<u64>, Vec<u64>, Height), Error> {
    // get the packet commitments on the counterparty/ source chain
    let commitments_request = QueryPacketCommitmentsRequest {
        port_id: src_port_id.to_string(),
        channel_id: src_channel_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let (commitments, src_response_height) = src_chain
        .query_packet_commitments(commitments_request)
        .map_err(Error::relayer)?;

    let commit_sequences: Vec<u64> = commitments.into_iter().map(|v| v.sequence).collect();
    if commit_sequences.is_empty() {
        return Ok((commit_sequences, vec![], src_response_height));
    }

    let request = QueryUnreceivedPacketsRequest {
        port_id: dst_port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_commitment_sequences: commit_sequences.clone(),
    };

    let sequences = dst_chain
        .query_unreceived_packets(request)
        .map_err(Error::relayer)?;

    Ok((commit_sequences, sequences, src_response_height))
}

pub fn unreceived_acknowledgements(
    chain: &impl ChainHandle,
    counterparty_chain: &impl ChainHandle,
    channel: IdentifiedChannelEnd,
) -> Result<Vec<u64>, Error> {
    let counterparty_channel_id = channel
        .channel_end
        .counterparty()
        .channel_id
        .as_ref()
        .ok_or_else(Error::missing_counterparty_channel_id)?;

    let (_, sequences, _) = unreceived_acknowledgements_sequences(
        counterparty_chain,
        counterparty_channel_id,
        &channel.channel_end.counterparty().port_id,
        chain,
        &channel.channel_id,
        &channel.port_id,
    )?;

    Ok(sequences)
}

pub(crate) fn unreceived_acknowledgements_sequences(
    src_chain: &impl ChainHandle,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
    dst_chain: &impl ChainHandle,
    dst_channel_id: &ChannelId,
    dst_port_id: &PortId,
) -> Result<(Vec<u64>, Vec<u64>, Height), Error> {
    // get the packet acknowledgments on counterparty/source chain
    let acks_request = QueryPacketAcknowledgementsRequest {
        port_id: src_port_id.to_string(),
        channel_id: src_channel_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let (acks, src_response_height) = src_chain
        .query_packet_acknowledgements(acks_request)
        .map_err(Error::relayer)?;

    let mut acked_sequences: Vec<u64> = acks.into_iter().map(|v| v.sequence).collect();
    if acked_sequences.is_empty() {
        return Ok((acked_sequences, vec![], src_response_height));
    }

    acked_sequences.sort_unstable();

    let request = QueryUnreceivedAcksRequest {
        port_id: dst_port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_ack_sequences: acked_sequences.clone(),
    };

    let sequences = dst_chain
        .query_unreceived_acknowledgement(request)
        .map_err(Error::relayer)?;

    Ok((acked_sequences, sequences, src_response_height))
}
