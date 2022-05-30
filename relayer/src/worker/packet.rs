use core::time::Duration;
use std::sync::{Arc, Mutex};

use crossbeam_channel::Receiver;
use tracing::{error_span, trace};

use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::event::monitor::EventBatch;
use crate::foreign_client::HasExpiredOrFrozenError;
use crate::link::Resubmit;
use crate::link::{error::LinkError, Link};
use crate::object::Packet;
use crate::telemetry;
use crate::util::retry::{retry_with_index, RetryResult};
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::worker::retry_strategy;

use super::error::RunError;
use super::WorkerCmd;

fn handle_link_error_in_task(e: LinkError) -> TaskError<RunError> {
    if e.is_expired_or_frozen_error() {
        TaskError::Fatal(RunError::link(e))
    } else {
        TaskError::Ignore(RunError::link(e))
    }
}

/// Spawns a packet worker task in the background that handles the work of
/// processing pending txs between `ChainA` and `ChainB`.
pub fn spawn_packet_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    path: Packet,
    // Mutex is used to prevent race condition between the packet workers
    link: Arc<Mutex<Link<ChainA, ChainB>>>,
    resubmit: Resubmit,
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
        let relay_path = &mut link.lock().unwrap().a_to_b;

        relay_path
            .refresh_schedule()
            .map_err(handle_link_error_in_task)?;

        relay_path
            .execute_schedule()
            .map_err(handle_link_error_in_task)?;

        let summary = relay_path.process_pending_txs(resubmit);

        if !summary.is_empty() {
            trace!("packet worker produced relay summary: {}", summary);
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
    clear_interval: u64,
    path: Packet,
) -> TaskHandle {
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
            retry_with_index(retry_strategy::worker_stubborn_strategy(), |i| {
                let result = handle_packet_cmd(
                    &mut link.lock().unwrap(),
                    clear_interval,
                    &path,
                    cmd.clone(),
                );

                match result {
                    Ok(()) => RetryResult::Ok(()),
                    Err(TaskError::Ignore(_)) => RetryResult::Retry(i),
                    Err(TaskError::Fatal(_)) => RetryResult::Err(i),
                }
            })
            .map_err(|e| TaskError::Fatal(RunError::retry(e)))?;
        }

        Ok(Next::Continue)
    })
}

pub fn spawn_clear_packet_on_start_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: Arc<Mutex<Link<ChainA, ChainB>>>,
    clear_interval: u64,
    path: Packet,
) -> TaskHandle {
    let span = {
        let relay_path = &link.lock().unwrap().a_to_b;
        error_span!(
            "clear_packet_on_start",
            src_chain = %relay_path.src_chain().id(),
            src_port = %relay_path.src_port_id(),
            src_channel = %relay_path.src_channel_id(),
            dst_chain = %relay_path.dst_chain().id(),
        )
    };

    spawn_background_task(span, Some(Duration::from_secs(1)), move || {
        handle_clear_packet(&mut link.lock().unwrap(), clear_interval, &path, None)?;

        Ok(Next::Abort)
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
    link: &mut Link<ChainA, ChainB>,
    clear_interval: u64,
    path: &Packet,
    cmd: WorkerCmd,
) -> Result<(), TaskError<RunError>> {
    match cmd {
        WorkerCmd::IbcEvents { batch } => handle_update_schedule(link, clear_interval, path, batch),

        // Handle the arrival of an event signaling that the
        // source chain has advanced to a new block.
        WorkerCmd::NewBlock {
            height,
            new_block: _,
        } => {
            // Decide if packet clearing should be scheduled.
            // Packet clearing may happen once at start,
            // and then at predefined block intervals.
            if should_clear_packets(clear_interval, height) {
                handle_clear_packet(link, clear_interval, path, Some(height))
            } else {
                Ok(())
            }
        }

        WorkerCmd::ClearPendingPackets => handle_clear_packet(link, clear_interval, path, None),
    }
}

/// Whether or not to clear pending packets at this `step` for the given height.
/// Packets are cleared on the first iteration if this is an ordered channel, or
/// if `clear_on_start` is true.
/// Subsequently, packets are cleared only if `clear_interval` is not `0` and
/// if we have reached the interval.
fn should_clear_packets(clear_interval: u64, height: Height) -> bool {
    clear_interval != 0 && height.revision_height % clear_interval == 0
}

fn handle_update_schedule<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    clear_interval: u64,
    path: &Packet,
    batch: EventBatch,
) -> Result<(), TaskError<RunError>> {
    link.a_to_b
        .update_schedule(batch)
        .map_err(handle_link_error_in_task)?;

    handle_execute_schedule(link, clear_interval, path)
}

fn handle_clear_packet<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    clear_interval: u64,
    path: &Packet,
    height: Option<Height>,
) -> Result<(), TaskError<RunError>> {
    link.a_to_b
        .schedule_packet_clearing(height)
        .map_err(handle_link_error_in_task)?;

    handle_execute_schedule(link, clear_interval, path)
}

fn handle_execute_schedule<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    clear_interval: u64,
    path: &Packet,
) -> Result<(), TaskError<RunError>> {
    link.a_to_b
        .refresh_schedule()
        .map_err(handle_link_error_in_task)?;

    link.a_to_b
        .execute_schedule()
        .map_err(handle_link_error_in_task)?;

    let resubmit = Resubmit::from_clear_interval(clear_interval);

    let summary = link.a_to_b.process_pending_txs(resubmit);

    if !summary.is_empty() {
        trace!("produced relay summary: {:?}", summary);
    }

    telemetry!(packet_metrics(path, &summary));

    Ok(())
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
