use std::convert::TryInto;
use std::thread;
use std::time::{Duration, Instant};

use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use tracing::{error_span, info};

use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height;

use crate::chain::counterparty::{unreceived_acknowledgements, unreceived_packets};
use crate::chain::handle::ChainHandle;
use crate::chain::requests::Qualified;
use crate::chain::tracking::TrackingId;
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::link::error::LinkError;
use crate::link::operational_data::{OperationalData, TrackedEvents};
use crate::link::packet_events::{
    query_packet_events_with, query_send_packet_events, query_write_ack_events,
};
use crate::link::relay_path::RelayPath;
use crate::link::relay_sender::SyncSender;
use crate::link::Link;
use crate::path::PathIdentifiers;
use crate::util::pretty::{PrettyDuration, PrettySlice};

impl<ChainA: ChainHandle, ChainB: ChainHandle> RelayPath<ChainA, ChainB> {
    /// Fetches an operational data that has fulfilled its predefined delay period. May _block_
    /// waiting for the delay period to pass.
    /// Returns `Ok(None)` if there is no operational data scheduled.
    pub(crate) fn fetch_scheduled_operational_data(
        &self,
    ) -> Result<Option<OperationalData>, LinkError> {
        if let Some(odata) = self.src_operational_data.pop_front() {
            Ok(Some(wait_for_conn_delay(
                odata,
                &|| self.src_time_latest(),
                &|| self.src_max_block_time(),
                &|| self.src_latest_height(),
            )?))
        } else if let Some(odata) = self.dst_operational_data.pop_front() {
            Ok(Some(wait_for_conn_delay(
                odata,
                &|| self.dst_time_latest(),
                &|| self.dst_max_block_time(),
                &|| self.dst_latest_height(),
            )?))
        } else {
            Ok(None)
        }
    }

    /// Given a vector of [`OperationalData`], this method proceeds to relaying
    /// all the messages therein. It accumulates all events generated in the
    /// mutable vector of [`IbcEvent`]s.
    pub fn relay_and_accumulate_results(
        &self,
        from: Vec<OperationalData>,
        results: &mut Vec<IbcEvent>,
    ) -> Result<(), LinkError> {
        for od in from {
            let mut last_res = self.relay_from_operational_data::<SyncSender>(od)?;
            results.append(&mut last_res.events);
        }

        Ok(())
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Link<ChainA, ChainB> {
    pub fn relay_recv_packet_and_timeout_messages(&self) -> Result<Vec<IbcEvent>, LinkError> {
        self.relay_recv_packet_and_timeout_messages_with_packet_data_query_height(None)
    }
    /// Implements the `packet-recv` CLI
    pub fn relay_recv_packet_and_timeout_messages_with_packet_data_query_height(
        &self,
        packet_data_query_height: Option<Height>,
    ) -> Result<Vec<IbcEvent>, LinkError> {
        let _span = error_span!(
            "relay_recv_packet_and_timeout_messages",
            src_chain = %self.a_to_b.src_chain().id(),
            src_port = %self.a_to_b.src_port_id(),
            src_channel = %self.a_to_b.src_channel_id(),
            dst_chain = %self.a_to_b.dst_chain().id(),
        )
        .entered();

        // Find the sequence numbers of unreceived packets
        let (sequences, src_response_height) = unreceived_packets(
            self.a_to_b.dst_chain(),
            self.a_to_b.src_chain(),
            &self.a_to_b.path_id,
        )
        .map_err(LinkError::supervisor)?;

        if sequences.is_empty() {
            return Ok(vec![]);
        }

        info!(
            "{} unreceived packets found: {} ",
            sequences.len(),
            PrettySlice(&sequences)
        );

        let query_height = match packet_data_query_height {
            Some(height) => Qualified::Equal(height),
            None => Qualified::SmallerEqual(src_response_height),
        };

        self.relay_packet_messages(
            sequences,
            query_height,
            query_send_packet_events,
            TrackingId::new_static("packet-recv"),
        )
    }

    pub fn relay_ack_packet_messages(&self) -> Result<Vec<IbcEvent>, LinkError> {
        self.relay_ack_packet_messages_with_packet_data_query_height(None)
    }

    /// Implements the `packet-ack` CLI
    pub fn relay_ack_packet_messages_with_packet_data_query_height(
        &self,
        packet_data_query_height: Option<Height>,
    ) -> Result<Vec<IbcEvent>, LinkError> {
        let _span = error_span!(
            "relay_ack_packet_messages",
            src_chain = %self.a_to_b.src_chain().id(),
            src_port = %self.a_to_b.src_port_id(),
            src_channel = %self.a_to_b.src_channel_id(),
            dst_chain = %self.a_to_b.dst_chain().id(),
        )
        .entered();

        // Find the sequence numbers of unreceived acknowledgements
        let (sequences, src_response_height) = unreceived_acknowledgements(
            self.a_to_b.dst_chain(),
            self.a_to_b.src_chain(),
            &self.a_to_b.path_id,
        )
        .map_err(LinkError::supervisor)?;

        if sequences.is_empty() {
            return Ok(vec![]);
        }

        info!(
            "{} unreceived acknowledgements found: {} ",
            sequences.len(),
            PrettySlice(&sequences)
        );

        let query_height = match packet_data_query_height {
            Some(height) => Qualified::Equal(height),
            None => Qualified::SmallerEqual(src_response_height),
        };

        self.relay_packet_messages(
            sequences,
            query_height,
            query_write_ack_events,
            TrackingId::new_static("packet-ack"),
        )
    }

    fn relay_packet_messages<QueryFn>(
        &self,
        sequences: Vec<Sequence>,
        query_height: Qualified<Height>,
        query_fn: QueryFn,
        tracking_id: TrackingId,
    ) -> Result<Vec<IbcEvent>, LinkError>
    where
        QueryFn: Fn(
            &ChainA,
            &PathIdentifiers,
            &[Sequence],
            Qualified<Height>,
        ) -> Result<Vec<IbcEventWithHeight>, Error>,
    {
        let event_chunks = query_packet_events_with(
            &sequences,
            query_height,
            self.a_to_b.src_chain(),
            &self.a_to_b.path_id,
            query_fn,
        );

        let mut results = vec![];

        for event_chunk in event_chunks {
            let tracked_events = TrackedEvents::new(event_chunk, tracking_id);
            self.a_to_b.events_to_operational_data(tracked_events)?;

            // In case of zero connection delay, the op. data will already be ready
            let (src_ods, dst_ods) = self.a_to_b.try_fetch_scheduled_operational_data()?;
            self.a_to_b
                .relay_and_accumulate_results(Vec::from(src_ods), &mut results)?;
            self.a_to_b
                .relay_and_accumulate_results(Vec::from(dst_ods), &mut results)?;
        }

        // In case of non-zero connection delay, we block here waiting for all op.data
        // until the connection delay elapses
        while let Some(odata) = self.a_to_b.fetch_scheduled_operational_data()? {
            self.a_to_b
                .relay_and_accumulate_results(vec![odata], &mut results)?;
        }

        Ok(results)
    }
}

fn wait_for_conn_delay<ChainTime, MaxBlockTime, LatestHeight>(
    odata: OperationalData,
    chain_time: &ChainTime,
    max_expected_time_per_block: &MaxBlockTime,
    latest_height: &LatestHeight,
) -> Result<OperationalData, LinkError>
where
    ChainTime: Fn() -> Result<Instant, LinkError>,
    MaxBlockTime: Fn() -> Result<Duration, LinkError>,
    LatestHeight: Fn() -> Result<Height, LinkError>,
{
    let (time_left, blocks_left) =
        odata.conn_delay_remaining(chain_time, max_expected_time_per_block, latest_height)?;

    match (time_left, blocks_left) {
        (Duration::ZERO, 0) => {
            info!(
                "ready to fetch a scheduled op. data with batch of size {} targeting {}",
                odata.batch.len(),
                odata.target,
            );
            Ok(odata)
        }
        (Duration::ZERO, blocks_left) => {
            info!(
                    "waiting ({} blocks left) for a scheduled op. data with batch of size {} targeting {}",
                    blocks_left,
                    odata.batch.len(),
                    odata.target,
                );

            let blocks_left: u32 = blocks_left.try_into().expect("blocks_left > u32::MAX");

            // Wait until the delay period passes
            thread::sleep(blocks_left * max_expected_time_per_block()?);

            Ok(odata)
        }
        (time_left, _) => {
            info!(
                "waiting ({} left) for a scheduled op. data with batch of size {} targeting {}",
                PrettyDuration(&time_left),
                odata.batch.len(),
                odata.target,
            );

            // Wait until the delay period passes
            thread::sleep(time_left);

            // `blocks_left` maybe non-zero, so recurse to recheck that all delays are handled.
            wait_for_conn_delay(
                odata,
                chain_time,
                max_expected_time_per_block,
                latest_height,
            )
        }
    }
}
