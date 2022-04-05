use std::convert::TryInto;
use std::thread;
use std::time::{Duration, Instant};

use ibc::events::IbcEvent;
use ibc::Height;
use tracing::{error_span, info};

use crate::chain::handle::ChainHandle;
use crate::link::error::LinkError;
use crate::link::operational_data::OperationalData;
use crate::link::relay_path::RelayPath;
use crate::link::{relay_sender, Link};

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
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Link<ChainA, ChainB> {
    /// Implements the `packet-recv` CLI
    pub fn build_and_send_recv_packet_messages(&self) -> Result<Vec<IbcEvent>, LinkError> {
        let _span = error_span!(
            "PacketRecvCmd",
            src_chain = %self.a_to_b.src_chain().id(),
            src_port = %self.a_to_b.src_port_id(),
            src_channel = %self.a_to_b.src_channel_id(),
            dst_chain = %self.a_to_b.dst_chain().id(),
        )
        .entered();

        self.a_to_b.build_recv_packet_and_timeout_msgs(None)?;

        let mut results = vec![];

        // Block waiting for all of the scheduled data (until `None` is returned)
        while let Some(odata) = self.a_to_b.fetch_scheduled_operational_data()? {
            let mut last_res = self
                .a_to_b
                .relay_from_operational_data::<relay_sender::SyncSender>(odata)?;
            results.append(&mut last_res.events);
        }

        Ok(results)
    }

    /// Implements the `packet-ack` CLI
    pub fn build_and_send_ack_packet_messages(&self) -> Result<Vec<IbcEvent>, LinkError> {
        let _span = error_span!(
            "PacketAckCmd",
            src_chain = %self.a_to_b.src_chain().id(),
            src_port = %self.a_to_b.src_port_id(),
            src_channel = %self.a_to_b.src_channel_id(),
            dst_chain = %self.a_to_b.dst_chain().id(),
        )
        .entered();

        self.a_to_b.build_packet_ack_msgs(None)?;

        let mut results = vec![];

        // Block waiting for all of the scheduled data
        while let Some(odata) = self.a_to_b.fetch_scheduled_operational_data()? {
            let mut last_res = self
                .a_to_b
                .relay_from_operational_data::<relay_sender::SyncSender>(odata)?;
            results.append(&mut last_res.events);
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
                    "waiting ({:?} blocks left) for a scheduled op. data with batch of size {} targeting {}",
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
                "waiting ({:?} left) for a scheduled op. data with batch of size {} targeting {}",
                time_left,
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
