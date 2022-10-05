//! Utility methods for querying packet event data.

use std::cmp::Ordering;

use tracing::{info, span, trace, warn, Level};

use ibc::core::ics04_channel::packet::Sequence;
use ibc::events::{IbcEvent, WithBlockDataType};
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    QueryBlockRequest, QueryHeight, QueryPacketEventDataRequest, QueryTxRequest,
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
    strict_query_height: bool,
    src_chain: &'a ChainA,
    path: &'a PathIdentifiers,
    query_fn: impl Fn(&ChainA, &PathIdentifiers, &[Sequence], Height, bool) -> Result<Vec<IbcEvent>, LinkError>
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
            match query_fn(src_chain, path, chunk, query_height, strict_query_height) {
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
    mut query: QueryPacketEventDataRequest,
) -> Result<Vec<IbcEvent>, LinkError> {
    let tx_events = src_chain
        .query_txs(QueryTxRequest::Packet(query.clone()))
        .map_err(LinkError::relayer)?;

    let recvd_sequences: Vec<_> = tx_events
        .iter()
        .filter_map(|eh| eh.event.packet().map(|p| p.sequence))
        .collect();

    query.sequences.retain(|seq| !recvd_sequences.contains(seq));

    let (start_block_events, end_block_events) = if !query.sequences.is_empty() {
        src_chain
            .query_blocks(QueryBlockRequest::Packet(query))
            .map_err(LinkError::relayer)?
    } else {
        Default::default()
    };

    trace!("start_block_events {:?}", start_block_events);
    trace!("tx_events {:?}", tx_events);
    trace!("end_block_events {:?}", end_block_events);

    // Events should be ordered in the following fashion,
    // for any two blocks b1, b2 at height h1, h2 with h1 < h2:
    // b1.start_block_events
    // b1.tx_events
    // b1.end_block_events
    // b2.start_block_events
    // b2.tx_events
    // b2.end_block_events
    //
    // As of now, we just sort them by sequence number which should
    // yield a similar result and will revisit this approach in the future.
    let mut events = vec![];

    events.extend(start_block_events);
    events.extend(tx_events);
    events.extend(end_block_events);

    events.sort_by(|a, b| {
        a.event
            .packet()
            .zip(b.event.packet())
            .map(|(pa, pb)| pa.sequence.cmp(&pb.sequence))
            .unwrap_or(Ordering::Equal)
    });

    Ok(events.into_iter().map(|e| e.event).collect())
}

/// Returns relevant packet events for building RecvPacket and timeout messages
/// for the given vector of packet [`Sequence`] numbers.
pub fn query_send_packet_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: &[Sequence],
    src_query_height: Height,
    strict_query_height: bool,
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
        strict_query_height,
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
    strict_query_height: bool,
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
        strict_query_height,
    };

    query_packet_events(src_chain, query)
}
