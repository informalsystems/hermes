use core::time::Duration;
use std::sync::{Arc, Mutex};

use crossbeam_channel::Receiver;
use tracing::{error, error_span, trace, warn};

use ibc::core::ics04_channel::channel::Order;
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::foreign_client::HasExpiredOrFrozenError;
use crate::link::{error::LinkError, Link};
use crate::object::Packet;
use crate::telemetry;
use crate::util::retry::{retry_with_index, RetryResult};
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::worker::retry_strategy;

use super::error::RunError;
use super::WorkerCmd;

/// Whether or not to clear pending packets at this `step` for the given height.
/// Packets are cleared on the first iteration if this is an ordered channel, or
/// if `clear_on_start` is true.
/// Subsequently, packets are cleared only if `clear_interval` is not `0` and
/// if we have reached the interval.
fn should_clear_packets(
    is_first_run: &mut bool,
    clear_on_start: bool,
    channel_ordering: Order,
    clear_interval: u64,
    height: Height,
) -> bool {
    if *is_first_run {
        *is_first_run = false;
        if channel_ordering == Order::Ordered {
            warn!("ordered channel: will clear packets because this is the first run");
            true
        } else {
            clear_on_start
        }
    } else {
        clear_interval != 0 && height.revision_height % clear_interval == 0
    }
}

fn handle_link_error_in_task(e: LinkError) -> TaskError<RunError> {
    if e.is_expired_or_frozen_error() {
        TaskError::Fatal(RunError::link(e))
    } else {
        TaskError::Ignore(RunError::link(e))
    }
}

pub fn spawn_packet_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    path: Packet,
    // Mutex is used to prevent race condition between the packet workers
    link: Arc<Mutex<Link<ChainA, ChainB>>>,
) -> TaskHandle {
    let span = {
        let relay_path = &link.lock().unwrap().a_to_b;
        error_span!(
            "packet",
            src_chain = %relay_path.src_chain().id(),
            src_port = %relay_path.src_port_id(),
            src_channel = %relay_path.src_channel_id(),
            dst_chain = %relay_path.dst_chain().id(),
        )
    };

    spawn_background_task(span, Some(Duration::from_millis(1000)), move || {
        let relay_path = &link.lock().unwrap().a_to_b;

        relay_path
            .refresh_schedule()
            .map_err(handle_link_error_in_task)?;

        relay_path
            .execute_schedule()
            .map_err(handle_link_error_in_task)?;

        let summary = relay_path.process_pending_txs();

        if !summary.is_empty() {
            trace!("Packet worker produced relay summary: {:?}", summary);
        }

        telemetry!(packet_metrics(&path, &summary));
        let _path = &path; // avoid unused variable warning when telemetry is disabled

        Ok(Next::Continue)
    })
}

pub fn spawn_packet_cmd_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    cmd_rx: Receiver<WorkerCmd>,
    // Mutex is used to prevent race condition between the packet workers
    link: Arc<Mutex<Link<ChainA, ChainB>>>,
    clear_on_start: bool,
    clear_interval: u64,
    path: Packet,
) -> TaskHandle {
    let mut is_first_run: bool = true;
    let span = {
        let relay_path = &link.lock().unwrap().a_to_b;
        error_span!(
            "packet_cmd",
            src_chain = %relay_path.src_chain().id(),
            src_port = %relay_path.src_port_id(),
            src_channel = %relay_path.src_channel_id(),
            dst_chain = %relay_path.dst_chain().id(),
        )
    };
    spawn_background_task(span, Some(Duration::from_millis(200)), move || {
        if let Ok(cmd) = cmd_rx.try_recv() {
            retry_with_index(retry_strategy::worker_stubborn_strategy(), |index| {
                handle_packet_cmd(
                    &mut is_first_run,
                    &link.lock().unwrap(),
                    clear_on_start,
                    clear_interval,
                    &path,
                    cmd.clone(),
                    index,
                )
            })
            .map_err(|e| TaskError::Fatal(RunError::retry(e)))?;
        }

        Ok(Next::Continue)
    })
}

/// Receives worker commands, which may be:
///     - IbcEvent => then it updates schedule
///     - NewBlock => schedules packet clearing
///     - Shutdown => exits
///
/// Regardless of the incoming command, this method
/// also refreshes and executes any scheduled operational
/// data that is ready.
fn handle_packet_cmd<ChainA: ChainHandle, ChainB: ChainHandle>(
    is_first_run: &mut bool,
    link: &Link<ChainA, ChainB>,
    clear_on_start: bool,
    clear_interval: u64,
    path: &Packet,
    cmd: WorkerCmd,
    index: u64,
) -> RetryResult<(), u64> {
    trace!("handling command {:?}", cmd);
    let result = match cmd {
        WorkerCmd::IbcEvents { batch } => link.a_to_b.update_schedule(batch),

        // Handle the arrival of an event signaling that the
        // source chain has advanced to a new block.
        WorkerCmd::NewBlock {
            height,
            new_block: _,
        } => {
            // Decide if packet clearing should be scheduled.
            // Packet clearing may happen once at start,
            // and then at predefined block intervals.
            if should_clear_packets(
                is_first_run,
                clear_on_start,
                link.a_to_b.channel().ordering,
                clear_interval,
                height,
            ) {
                link.a_to_b.schedule_packet_clearing(Some(height))
            } else {
                Ok(())
            }
        }

        WorkerCmd::ClearPendingPackets => link.a_to_b.schedule_packet_clearing(None),
    };

    if let Err(e) = result {
        error!(
            path = %path.short_name(),
            retry_index = %index,
            "will retry: handling command encountered error: {}",
            e
        );

        return RetryResult::Retry(index);
    }

    // The calls to refresh_schedule and execute_schedule depends on
    // earlier calls to update_schedule and schedule_packet_clearing.
    // Hence they must be retried in the same function body so that
    // the same WorkerCmd is used for retrying the whole execution.
    //
    // The worker for spawn_packet_worker is still needed to handle
    // the case when no PacketCmd arriving, so that it can still
    // do the refresh and execute schedule.
    // This follows the original logic here:
    // https://github.com/informalsystems/ibc-rs/blob/e7a6403888f48754ddb80e35ebe2281fb7c51c04/relayer/src/worker/packet.rs#L127-L133

    let schedule_result = link
        .a_to_b
        .refresh_schedule()
        .and_then(|_| link.a_to_b.execute_schedule());

    if let Err(e) = schedule_result {
        if e.is_expired_or_frozen_error() {
            error!("aborting due to expired or frozen client");
            return RetryResult::Err(index);
        } else {
            error!(
                retry_index = %index,
                "will retry: schedule execution encountered error: {}",
                e,
            );
            return RetryResult::Retry(index);
        }
    }

    let summary = link.a_to_b.process_pending_txs();

    if !summary.is_empty() {
        trace!("produced relay summary: {:?}", summary);
    }

    telemetry!(packet_metrics(path, &summary));

    RetryResult::Ok(())
}

#[cfg(feature = "telemetry")]
use crate::link::RelaySummary;

#[cfg(feature = "telemetry")]
fn packet_metrics(path: &Packet, summary: &RelaySummary) {
    receive_packet_metrics(path, summary);
    acknowledgment_metrics(path, summary);
    timeout_metrics(path, summary);
}

#[cfg(feature = "telemetry")]
fn receive_packet_metrics(path: &Packet, summary: &RelaySummary) {
    use ibc::events::IbcEvent::WriteAcknowledgement;

    let count = summary
        .events
        .iter()
        .filter(|e| matches!(e, WriteAcknowledgement(_)))
        .count();

    telemetry!(
        ibc_receive_packets,
        &path.src_chain_id,
        &path.src_channel_id,
        &path.src_port_id,
        count as u64,
    );
}

#[cfg(feature = "telemetry")]
fn acknowledgment_metrics(path: &Packet, summary: &RelaySummary) {
    use ibc::events::IbcEvent::AcknowledgePacket;

    let count = summary
        .events
        .iter()
        .filter(|e| matches!(e, AcknowledgePacket(_)))
        .count();

    telemetry!(
        ibc_acknowledgment_packets,
        &path.src_chain_id,
        &path.src_channel_id,
        &path.src_port_id,
        count as u64,
    );
}

#[cfg(feature = "telemetry")]
fn timeout_metrics(path: &Packet, summary: &RelaySummary) {
    use ibc::events::IbcEvent::TimeoutPacket;
    let count = summary
        .events
        .iter()
        .filter(|e| matches!(e, TimeoutPacket(_)))
        .count();

    telemetry!(
        ibc_timeout_packets,
        &path.src_chain_id,
        &path.src_channel_id,
        &path.src_port_id,
        count as u64,
    );
}
