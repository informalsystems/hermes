//! Utility methods for querying packet event data.

use itertools::Itertools;
use tracing::{info, span, warn, Level};

use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::events::WithBlockDataType;
use ibc_relayer_types::Height;

use crate::chain::handle::ChainHandle;
use crate::chain::requests::{Qualified, QueryHeight, QueryPacketEventDataRequest};
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::path::PathIdentifiers;
use crate::util::collate::CollatedIterExt;

/// Limit on how many query results should be expected.
pub const CHUNK_LENGTH: usize = 50;

/// Returns an iterator on batches of packet events.
pub fn query_packet_events_with<'a, ChainA, QueryFn>(
    sequences: &'a [Sequence],
    query_height: Qualified<Height>,
    src_chain: &'a ChainA,
    path: &'a PathIdentifiers,
    query_fn: QueryFn,
) -> impl Iterator<Item = Vec<IbcEventWithHeight>> + 'a
where
    ChainA: ChainHandle,
    QueryFn: Fn(
            &ChainA,
            &PathIdentifiers,
            &[Sequence],
            Qualified<Height>,
        ) -> Result<Vec<IbcEventWithHeight>, Error>
        + 'a,
{
    let events_total = sequences.len();
    let mut events_left = events_total;

    sequences.chunks(CHUNK_LENGTH).map_while(move |chunk| {
        match query_fn(src_chain, path, chunk, query_height) {
            Ok(events) => {
                events_left -= chunk.len();

                info!(
                    events.total = %events_total,
                    events.left = %events_left,
                    "pulled packet data for {} events out of {} sequences: {};",
                    events.len(),
                    chunk.len(),
                    chunk.iter().copied().collated().format(", "),
                );

                // Because we use the first event height to do the client update,
                // if the heights of the events differ, we get proof verification failures.
                // Therefore we overwrite the events height with the query height,
                // ie. the height of the first event.
                let events = events
                    .into_iter()
                    .map(|ev| ev.with_height(query_height.get()))
                    .collect();

                Some(events)
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
) -> Result<Vec<IbcEventWithHeight>, Error> {
    src_chain.query_packet_events(query)
}

/// Returns relevant packet events for building RecvPacket and timeout messages
/// for the given vector of packet [`Sequence`] numbers.
pub fn query_send_packet_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: &[Sequence],
    src_query_height: Qualified<Height>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
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
        height: src_query_height.map(QueryHeight::Specific),
    };

    query_packet_events(src_chain, query)
}

/// Returns packet event data for building ack messages for the
/// given list of [`Sequence`] numbers.
pub fn query_write_ack_events<ChainA: ChainHandle>(
    src_chain: &ChainA,
    path: &PathIdentifiers,
    sequences: &[Sequence],
    src_query_height: Qualified<Height>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
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
        height: src_query_height.map(QueryHeight::Specific),
    };

    query_packet_events(src_chain, query)
}
