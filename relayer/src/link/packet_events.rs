//! Utility methods for querying packet event data.

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

/// Limit on how many query results should be expected.
pub const QUERY_RESULT_LIMIT: usize = 50;

/// Returns an iterator on batches of packet events.
pub fn query_packet_events_with<'a, ChainA>(
    sequence_nrs: &'a [Sequence],
    query_height: Height,
    src_chain: &'a ChainA,
    path: &'a PathIdentifiers,
    query_fn: impl Fn(&ChainA, &PathIdentifiers, Vec<Sequence>, Height) -> Result<Vec<IbcEvent>, LinkError>
        + 'a,
) -> impl Iterator<Item = Vec<IbcEventWithHeight>> + 'a
where
    ChainA: ChainHandle,
{
    let events_total_count = sequence_nrs.len();
    let mut events_left_count = events_total_count;

    sequence_nrs
        .chunks(QUERY_RESULT_LIMIT)
        .map_while(move |c| {
            let sequences_nrs_chunk = c.to_vec();
            match query_fn(src_chain, path, sequences_nrs_chunk, query_height) {
                Ok(events) => {
                    events_left_count -= c.len();
                    info!(events_total = %events_total_count, events_left = %events_left_count, "pulled packet data for {} events;", events.len());

                    Some(events.into_iter().map(|ev| IbcEventWithHeight::new(ev, query_height)).collect())
                },
                Err(e) => {
                    warn!("encountered query failure while pulling packet data: {}", e);
                    None
                }
            }
        })
}

/// Returns relevant packet events for building RecvPacket and timeout messages
/// for the given vector of packet [`Sequence`] numbers.
pub fn query_send_packet_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: Vec<Sequence>,
    src_query_height: Height,
) -> Result<Vec<IbcEvent>, LinkError> {
    let mut events_result = vec![];
    let _span = span!(Level::DEBUG, "query_send_packet_events", h = %src_query_height).entered();

    let mut query = QueryPacketEventDataRequest {
        event_id: WithBlockDataType::SendPacket,
        source_port_id: path.counterparty_port_id.clone(),
        source_channel_id: path.counterparty_channel_id.clone(),
        destination_port_id: path.port_id.clone(),
        destination_channel_id: path.channel_id.clone(),
        sequences,
        height: QueryHeight::Specific(src_query_height),
    };

    let tx_events: Vec<IbcEvent> = src_chain
        .query_txs(QueryTxRequest::Packet(query.clone()))
        .map_err(LinkError::relayer)?
        .into_iter()
        .map(|ev_with_height| ev_with_height.event)
        .collect();

    let recvd_sequences: Vec<Sequence> = tx_events
        .iter()
        .filter_map(|ev| match ev {
            IbcEvent::SendPacket(ref send_ev) => Some(send_ev.packet.sequence),
            IbcEvent::WriteAcknowledgement(ref ack_ev) => Some(ack_ev.packet.sequence),
            _ => None,
        })
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

    // events must be ordered in the following fashion -
    // start-block events followed by tx-events followed by end-block events
    events_result.extend(start_block_events);
    events_result.extend(tx_events);
    events_result.extend(end_block_events);

    Ok(events_result)
}

/// Returns packet event data for building ack messages for the
/// given list of [`Sequence`] numbers.
pub fn query_write_ack_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: Vec<Sequence>,
    src_query_height: Height,
) -> Result<Vec<IbcEvent>, LinkError> {
    // TODO(Adi): Would be good to make use of generics.
    let events_result = src_chain
        .query_txs(QueryTxRequest::Packet(QueryPacketEventDataRequest {
            event_id: WithBlockDataType::WriteAck,
            source_port_id: path.port_id.clone(),
            source_channel_id: path.channel_id.clone(),
            destination_port_id: path.counterparty_port_id.clone(),
            destination_channel_id: path.counterparty_channel_id.clone(),
            sequences,
            height: QueryHeight::Specific(src_query_height),
        }))
        .map_err(|e| LinkError::query(src_chain.id(), e))?;

    Ok(events_result.into_iter().map(|ev| ev.event).collect())
}
