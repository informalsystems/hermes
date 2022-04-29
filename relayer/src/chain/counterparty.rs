use std::collections::HashSet;

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
    connection: &IdentifiedConnectionEnd,
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
            *channel_id,
            chain.id(),
        ));
    }

    let connection_id = channel_end
        .connection_hops()
        .first()
        .ok_or_else(|| Error::missing_connection_hops(*channel_id, chain.id()))?;

    let connection_end = chain
        .query_connection(connection_id, Height::zero())
        .map_err(Error::relayer)?;

    if !connection_end.is_open() {
        return Err(Error::connection_not_open(
            connection_id.clone(),
            *channel_id,
            chain.id(),
        ));
    }

    let client_id = connection_end.client_id();
    let client_state = chain
        .query_client_state(client_id, Height::zero())
        .map_err(Error::relayer)?;

    let client = IdentifiedAnyClientState::new(client_id.clone(), client_state);
    let connection = IdentifiedConnectionEnd::new(connection_id.clone(), connection_end);
    let channel = IdentifiedChannelEnd::new(port_id.clone(), *channel_id, channel_end);

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
                channel_id: *remote_channel_id,
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

/// Returns the sequences of the packet commitments on a given chain and channel (port_id + channel_id).
/// These are the sequences of the packets that were either:
///  - not yet received by the counterparty chain, or
///  - received on counterparty chain but not yet acknowledged by this chain,
pub fn commitments_on_chain(
    chain: &impl ChainHandle,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<(Vec<u64>, Height), Error> {
    // get the packet commitments on the counterparty/ source chain
    let commitments_request = QueryPacketCommitmentsRequest {
        port_id: port_id.to_string(),
        channel_id: channel_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let (commitments, response_height) = chain
        .query_packet_commitments(commitments_request)
        .map_err(Error::relayer)?;

    let mut commit_sequences: Vec<u64> = commitments.into_iter().map(|v| v.sequence).collect();
    commit_sequences.sort_unstable();
    Ok((commit_sequences, response_height))
}

/// Returns the sequences of the packets that were sent on the counterparty chain but for which
/// `MsgRecvPacket`-s have not been received on a given chain and channel (port_id + channel_id)
pub fn unreceived_packets_sequences(
    chain: &impl ChainHandle,
    port_id: &PortId,
    channel_id: &ChannelId,
    commitments_on_counterparty: Vec<u64>,
) -> Result<Vec<u64>, Error> {
    if commitments_on_counterparty.is_empty() {
        return Ok(vec![]);
    }

    let request = QueryUnreceivedPacketsRequest {
        port_id: port_id.to_string(),
        channel_id: channel_id.to_string(),
        packet_commitment_sequences: commitments_on_counterparty,
    };

    chain
        .query_unreceived_packets(request)
        .map_err(Error::relayer)
}

/// Returns the sequences of the written acknowledgments on a given chain and channel (port_id + channel_id), out of
/// the commitments still present on the counterparty chain.
pub fn packet_acknowledgements(
    chain: &impl ChainHandle,
    port_id: &PortId,
    channel_id: &ChannelId,
    commit_sequences: Vec<u64>,
) -> Result<(Vec<u64>, Height), Error> {
    let commit_set = commit_sequences.iter().cloned().collect::<HashSet<_>>();

    // Get the packet acknowledgments on counterparty/source chain
    let acks_request = QueryPacketAcknowledgementsRequest {
        port_id: port_id.to_string(),
        channel_id: channel_id.to_string(),
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
        packet_commitment_sequences: commit_sequences,
    };
    let (acks, response_height) = chain
        .query_packet_acknowledgements(acks_request)
        .map_err(Error::relayer)?;

    let mut acked_sequences: Vec<u64> = acks.into_iter().map(|v| v.sequence).collect();
    acked_sequences.retain(|s| commit_set.contains(s));
    acked_sequences.sort_unstable();

    Ok((acked_sequences, response_height))
}

/// Returns the sequences of the packets that were sent on the chain and for which:
///  - `MsgRecvPacket`-s have been received on the counterparty chain but
///  - `MsgAcknowledgement`-s have NOT been received by the chain
pub fn unreceived_acknowledgements_sequences(
    chain: &impl ChainHandle,
    port_id: &PortId,
    channel_id: &ChannelId,
    acks_on_counterparty: Vec<u64>,
) -> Result<Vec<u64>, Error> {
    if acks_on_counterparty.is_empty() {
        return Ok(vec![]);
    }

    let request = QueryUnreceivedAcksRequest {
        port_id: port_id.to_string(),
        channel_id: channel_id.to_string(),
        packet_ack_sequences: acks_on_counterparty,
    };

    chain
        .query_unreceived_acknowledgement(request)
        .map_err(Error::relayer)
}

/// This method returns a vector of sequence numbers for all the packets
/// which the counterparty chain _sent_ on the given channel and which the
/// (target) chain did not yet _receive_.
/// Expects an [`IdentifiedChannelEnd`] plus a pair of
/// [`ChainHandle`]s representing the chains at the two ends of this
/// channel, called a (target) chain and a counterparty chain.
///
/// ### Implementation details
/// This method involves two separate queries:
///
/// 1. It performs a [`QueryPacketCommitmentsRequest`] on the counterparty chain.
///     This query returns the vector of all sequence numbers for those packets that have
///     commitments written on-chain in the counterparty chain's state.
///
///     This step relies on [`commitments_on_chain`], see that method for more details.
///
/// 2. It performs a [`QueryUnreceivedPacketsRequest`] on the (target) chain.
///     Given the sequence numbers of packet commitments on the counterparty (query #1),
///     this query returns a subset of these sequence numbers, all of which the target
///     chain has not yet _received_.
///
///    This step relies on [`unreceived_packets_sequences`], see that method for more details.
///
pub fn unreceived_packets(
    chain: &impl ChainHandle,
    counterparty_chain: &impl ChainHandle,
    channel: &IdentifiedChannelEnd,
) -> Result<Vec<u64>, Error> {
    let counterparty = channel.channel_end.counterparty();
    let counterparty_channel_id = counterparty
        .channel_id
        .as_ref()
        .ok_or_else(Error::missing_counterparty_channel_id)?;

    let (commit_sequences, _) = commitments_on_chain(
        counterparty_chain,
        &counterparty.port_id,
        counterparty_channel_id,
    )?;

    unreceived_packets_sequences(
        chain,
        &channel.port_id,
        &channel.channel_id,
        commit_sequences,
    )
}

pub fn acknowledgements_on_chain(
    chain: &impl ChainHandle,
    counterparty_chain: &impl ChainHandle,
    channel: &IdentifiedChannelEnd,
) -> Result<(Vec<u64>, Height), Error> {
    let counterparty = channel.channel_end.counterparty();
    let counterparty_channel_id = counterparty
        .channel_id
        .as_ref()
        .ok_or_else(Error::missing_counterparty_channel_id)?;

    let (commitments_on_counterparty, _) = commitments_on_chain(
        counterparty_chain,
        &counterparty.port_id,
        counterparty_channel_id,
    )?;

    let (sequences, height) = packet_acknowledgements(
        chain,
        &channel.port_id,
        &channel.channel_id,
        commitments_on_counterparty,
    )?;

    Ok((sequences, height))
}

/// This method returns a vector of sequence numbers for those packets
/// which the counterparty chain _received_ on the given channel and which the
/// (target) chain did not yet _acknowledge_.
/// Expects an [`IdentifiedChannelEnd`] plus a pair of
/// [`ChainHandle`]s representing the chains at the two ends of this
/// channel, called a (target) chain and a counterparty chain.
///
/// ### Implementation details
/// This method involves two separate queries:
///
/// 1. It performs a [`QueryPacketCommitmentsRequest`] on the target chain.
///     This query returns the vector of all sequence numbers for those packets that have
///     commitments written on-chain in the (target) chain's state.
///
///     This step relies on [`commitments_on_chain`], see that method for more details.
///
/// 2. It performs a [`QueryPacketAcknowledgementsRequest`] on the counterparty chain.
///     Given the sequence numbers of packet commitments on the target chain (from step #1),
///     this query returns a subset of these sequence numbers, all of which the counterparty
///     chain has _received_ (i.e., it stores acknowledgments for these sequence numbers).
///
///     This step relies on [`packet_acknowledgements`], see that method for more details.
///
/// 3. It performs a [`QueryUnreceivedAcksRequest`] on the target chain.
///     Given the sequence numbers of packet acknowledgements on the counterparty (step #3),
///     this query fetches the subset among these acknowledgements which have not been
///     relayed yet to the target chain.
///     This step relies on [`unreceived_acknowledgements_sequences`].
pub fn unreceived_acknowledgements(
    chain: &impl ChainHandle,
    counterparty_chain: &impl ChainHandle,
    channel: &IdentifiedChannelEnd,
) -> Result<Vec<u64>, Error> {
    let counterparty = channel.channel_end.counterparty();
    let counterparty_channel_id = counterparty
        .channel_id
        .as_ref()
        .ok_or_else(Error::missing_counterparty_channel_id)?;

    let (commitments_on_src, _) =
        commitments_on_chain(chain, &channel.port_id, &channel.channel_id)?;

    let (acks_on_counterparty, _) = packet_acknowledgements(
        counterparty_chain,
        &counterparty.port_id,
        counterparty_channel_id,
        commitments_on_src,
    )?;

    unreceived_acknowledgements_sequences(
        chain,
        &channel.port_id,
        &channel.channel_id,
        acks_on_counterparty,
    )
}

/// A structure to display pending packet commitment IDs
/// at one end of a channel.
#[derive(Debug, Serialize)]
pub struct PendingPackets {
    /// Not yet received on the counterparty chain.
    pub unreceived_packets: Vec<u64>,
    /// Received on the counterparty chain,
    /// but the acknowledgement is not yet received on the local chain.
    pub unreceived_acks: Vec<u64>,
}

pub fn pending_packet_summary(
    chain: &impl ChainHandle,
    counterparty_chain: &impl ChainHandle,
    channel: &IdentifiedChannelEnd,
) -> Result<PendingPackets, Error> {
    let counterparty = channel.channel_end.counterparty();
    let counterparty_channel_id = counterparty
        .channel_id
        .as_ref()
        .ok_or_else(Error::missing_counterparty_channel_id)?;

    let (commitments_on_src, _) =
        commitments_on_chain(chain, &channel.port_id, &channel.channel_id)?;

    let unreceived = unreceived_packets_sequences(
        counterparty_chain,
        &counterparty.port_id,
        counterparty_channel_id,
        commitments_on_src.clone(),
    )?;

    let (acks_on_counterparty, _) = packet_acknowledgements(
        counterparty_chain,
        &counterparty.port_id,
        counterparty_channel_id,
        commitments_on_src,
    )?;

    let pending_acks = unreceived_acknowledgements_sequences(
        chain,
        &channel.port_id,
        &channel.channel_id,
        acks_on_counterparty,
    )?;

    Ok(PendingPackets {
        unreceived_packets: unreceived,
        unreceived_acks: pending_acks,
    })
}
