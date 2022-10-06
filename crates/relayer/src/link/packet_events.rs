//! Utility methods for querying packet event data.

use tracing::{info, span, warn, Level};

use ibc::core::ics04_channel::packet::Sequence;
use ibc::events::{IbcEvent, WithBlockDataType};
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    PacketQueryHeightQualifier, QueryHeight, QueryPacketEventDataRequest,
};
use crate::event::IbcEventWithHeight;
use crate::link::error::LinkError;
use crate::path::PathIdentifiers;
use crate::util::pretty::PrettySlice;

/// Limit on how many query results should be expected.
pub const QUERY_RESULT_LIMIT: usize = 50;

/// Returns an iterator on batches of packet events.
pub fn query_packet_events_with<'a, ChainA>(
    sequence_nrs: &'a [Sequence],
    query_height: Height,
    height_qualifier: PacketQueryHeightQualifier,
    src_chain: &'a ChainA,
    path: &'a PathIdentifiers,
    query_fn: impl Fn(
            &ChainA,
            &PathIdentifiers,
            &[Sequence],
            Height,
            PacketQueryHeightQualifier,
        ) -> Result<Vec<IbcEvent>, LinkError>
        + 'a,
) -> impl Iterator<Item = Vec<IbcEventWithHeight>> + 'a
where
    ChainA: ChainHandle,
{
    let events_total_count = sequence_nrs.len();
    let mut events_left_count = events_total_count;

    sequence_nrs
        .chunks(QUERY_RESULT_LIMIT)
        .map_while(move |chunk| {
            match query_fn(src_chain, path, chunk, query_height, height_qualifier) {
                Ok(events) => {
                    events_left_count -= chunk.len();

                    info!(
                        events.total = %events_total_count,
                        events.left = %events_left_count,
                        "pulled packet data for {} events out of {} sequences: {};",
                        events.len(),
                        chunk.len(),
                        PrettySlice(chunk)
                    );

                    Some(
                        events
                            .into_iter()
                            .map(|ev| IbcEventWithHeight::new(ev, query_height))
                            .collect(),
                    )
                }
                Err(e) => {
                    warn!("encountered query failure while pulling packet data: {}", e);
                    None
                }
            }
        })
}

fn query_packet_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    query: QueryPacketEventDataRequest,
) -> Result<Vec<IbcEvent>, LinkError> {
    let events = src_chain
        .query_packet_events(query)
        .map_err(LinkError::relayer)?;

    Ok(events.into_iter().map(|e| e.event).collect())
}

/// Returns relevant packet events for building RecvPacket and timeout messages
/// for the given vector of packet [`Sequence`] numbers.
pub fn query_send_packet_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: &[Sequence],
    src_query_height: Height,
    event_height_qualifier: PacketQueryHeightQualifier,
) -> Result<Vec<IbcEvent>, LinkError> {
    let _span = span!(
        Level::DEBUG,
        "query_send_packet_events",
        chain = %src_chain.id(),
        height = %src_query_height,
        ?sequences,
    )
    .entered();

    let query = QueryPacketEventDataRequest {
        event_id: WithBlockDataType::SendPacket,
        source_port_id: path.counterparty_port_id.clone(),
        source_channel_id: path.counterparty_channel_id.clone(),
        destination_port_id: path.port_id.clone(),
        destination_channel_id: path.channel_id.clone(),
        sequences: sequences.to_vec(),
        height: QueryHeight::Specific(src_query_height),
        event_height_qualifier,
    };

    query_packet_events(src_chain, query)
}

/// Returns packet event data for building ack messages for the
/// given list of [`Sequence`] numbers.
pub fn query_write_ack_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: &[Sequence],
    src_query_height: Height,
    event_height_qualifier: PacketQueryHeightQualifier,
) -> Result<Vec<IbcEvent>, LinkError> {
    let _span = span!(
        Level::DEBUG,
        "query_write_ack_packet_events",
        chain = %src_chain.id(),
        height = %src_query_height,
        ?sequences,
    )
    .entered();

    let query = QueryPacketEventDataRequest {
        event_id: WithBlockDataType::WriteAck,
        source_port_id: path.port_id.clone(),
        source_channel_id: path.channel_id.clone(),
        destination_port_id: path.counterparty_port_id.clone(),
        destination_channel_id: path.counterparty_channel_id.clone(),
        sequences: sequences.to_vec(),
        height: QueryHeight::Specific(src_query_height),
        event_height_qualifier,
    };

    query_packet_events(src_chain, query)
}
