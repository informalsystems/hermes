use core::time::Duration;
use std::sync::{Arc, Mutex};

use crossbeam_channel::Receiver;
use tracing::{error, error_span, trace};

use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::event::monitor::EventBatch;
use crate::foreign_client::HasExpiredOrFrozenError;
use crate::link::Resubmit;
use crate::link::{error::LinkError, Link};
use crate::object::Packet;
use crate::telemetry;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};

use super::error::RunError;
use super::WorkerCmd;

fn handle_link_error_in_task(e: LinkError) -> TaskError<RunError> {
    if e.is_expired_or_frozen_error() {
        // If the client is expired or frozen, terminate the packet worker
        // as there is no point of relaying further packets.
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
            "worker.packet",
            src_chain = %relay_path.src_chain().id(),
            src_port = %relay_path.src_port_id(),
            src_channel = %relay_path.src_channel_id(),
            dst_chain = %relay_path.dst_chain().id(),
        )
    };

    spawn_background_task(span, Some(Duration::from_millis(1000)), move || {
        handle_execute_schedule(&mut link.lock().unwrap(), &path, resubmit)?;
        Ok(Next::Continue)
    })
}

pub fn spawn_packet_cmd_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    cmd_rx: Receiver<WorkerCmd>,
    // Mutex is used to prevent race condition between the packet workers
    link: Arc<Mutex<Link<ChainA, ChainB>>>,
    mut should_clear_on_start: bool,
    clear_interval: u64,
    path: Packet,
) -> TaskHandle {
    let span = {
        let relay_path = &link.lock().unwrap().a_to_b;
        error_span!(
            "worker.packet.cmd",
            src_chain = %relay_path.src_chain().id(),
            src_port = %relay_path.src_port_id(),
            src_channel = %relay_path.src_channel_id(),
            dst_chain = %relay_path.dst_chain().id(),
        )
    };

    spawn_background_task(span, Some(Duration::from_millis(200)), move || {
        if let Ok(cmd) = cmd_rx.try_recv() {
            // Try to clear pending packets. At different levels down in `handle_packet_cmd` there
            // are retries mechanisms for MAX_RETRIES (current value hardcoded at 5).
            // If clearing fails after all these retries with ignorable error the task continues
            // (see `handle_link_error_in_task`) and clearing is retried with the next
            // (`NewBlock`) `cmd` that matches the clearing interval.
            handle_packet_cmd(
                &mut link.lock().unwrap(),
                &mut should_clear_on_start,
                clear_interval,
                &path,
                cmd,
            )?;
        }

        Ok(Next::Continue)
    })
}

/// Receives worker commands and handles them accordingly.
///
/// Given an `IbcEvent` command, updates the schedule and initiates
/// packet clearing if the `should_clear_on_start` flag has been toggled.
///
/// Given a `NewBlock` command, checks if packet clearing should occur
/// and performs it if so.
///
/// Given a `ClearPendingPackets` command, clears pending packets.
///
/// Regardless of the incoming command, this method also refreshes and
/// and executes any scheduled operational data that is ready.
fn handle_packet_cmd<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    should_clear_on_start: &mut bool,
    clear_interval: u64,
    path: &Packet,
    cmd: WorkerCmd,
) -> Result<(), TaskError<RunError>> {
    // Handle packet clearing which is triggered from a command
    let (do_clear, maybe_height) = match &cmd {
        WorkerCmd::IbcEvents { batch } => {
            if *should_clear_on_start {
                (true, Some(batch.height))
            } else {
                (false, None)
            }
        }

        // Handle the arrival of an event signaling that the
        // source chain has advanced to a new block
        WorkerCmd::NewBlock { height, .. } => {
            if *should_clear_on_start || should_clear_packets(clear_interval, *height) {
                (true, Some(*height))
            } else {
                (false, None)
            }
        }

        WorkerCmd::ClearPendingPackets => (true, None),
    };

    if do_clear {
        // Reset the `clear_on_start` flag and attempt packet clearing once now.
        // More clearing will be done at clear interval.
        if *should_clear_on_start {
            *should_clear_on_start = false;
        }
        handle_clear_packet(link, clear_interval, path, maybe_height)?;
    }

    // Handle command-specific task
    if let WorkerCmd::IbcEvents { batch } = cmd {
        handle_update_schedule(link, clear_interval, path, batch)
    } else {
        Ok(())
    }
}

/// Whether or not to clear pending packets at this `step` for some height.
/// If the relayer has been configured to clear packets on start and that has not
/// occurred yet, then packets are cleared.
///
/// If the specified height is reached, then packets are cleared if `clear_interval`
/// is not `0` and if we have reached the interval.
fn should_clear_packets(clear_interval: u64, height: Height) -> bool {
    clear_interval != 0 && height.revision_height() % clear_interval == 0
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

    handle_execute_schedule(link, path, Resubmit::from_clear_interval(clear_interval))
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

    handle_execute_schedule(link, path, Resubmit::from_clear_interval(clear_interval))
}

fn handle_execute_schedule<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    _path: &Packet,
    resubmit: Resubmit,
) -> Result<(), TaskError<RunError>> {
    link.a_to_b
        .refresh_schedule()
        .map_err(handle_link_error_in_task)?;

    link.a_to_b.execute_schedule().map_err(|e| {
        if e.is_expired_or_frozen_error() {
            TaskError::Fatal(RunError::link(e))
        } else {
            error!("will retry: schedule execution encountered error: {}", e,);
            TaskError::Ignore(RunError::link(e))
        }
    })?;

    let summary = link.a_to_b.process_pending_txs(resubmit);

    if !summary.is_empty() {
        trace!("produced relay summary: {:?}", summary);
        telemetry!(packet_metrics(_path, &summary));
    }

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
        receive_packets_confirmed,
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
        acknowledgment_packets_confirmed,
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
        timeout_packets_confirmed,
        &path.src_chain_id,
        &path.src_channel_id,
        &path.src_port_id,
        count as u64,
    );
}
