use core::time::Duration;
use itertools::Itertools;
use moka::sync::Cache;
use std::borrow::BorrowMut;
use std::sync::{Arc, Mutex};
use tracing::debug;

use crossbeam_channel::Receiver;
use ibc_proto::ibc::apps::fee::v1::{IdentifiedPacketFees, QueryIncentivizedPacketRequest};
use ibc_proto::ibc::core::channel::v1::PacketId;
use ibc_relayer_types::applications::ics29_fee::events::IncentivizedPacket;
use ibc_relayer_types::applications::transfer::{Amount, Coin, RawCoin};
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::events::{IbcEvent, IbcEventType};
use tracing::{error, error_span, trace};

use ibc_relayer_types::Height;

use crate::chain::handle::ChainHandle;
use crate::config::filter::FeePolicy;
use crate::event::monitor::EventBatch;
use crate::foreign_client::HasExpiredOrFrozenError;
use crate::link::Resubmit;
use crate::link::{error::LinkError, Link};
use crate::object::Packet;
use crate::telemetry;
use crate::util::lock::{LockExt, RwArc};
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};

use super::error::RunError;
use super::WorkerCmd;

const INCENTIVIZED_CACHE_TTL: Duration = Duration::from_secs(10 * 60);
const INCENTIVIZED_CACHE_MAX_CAPACITY: u64 = 1000;

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

pub fn spawn_incentivized_packet_cmd_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    cmd_rx: Receiver<WorkerCmd>,
    // Mutex is used to prevent race condition between the packet workers
    link: Arc<Mutex<Link<ChainA, ChainB>>>,
    path: Packet,
    fee_filter: FeePolicy,
) -> TaskHandle {
    let span = {
        let relay_path = &link.lock().unwrap().a_to_b;
        error_span!(
            "worker.incentivized.packet.cmd",
            src_chain = %relay_path.src_chain().id(),
            src_port = %relay_path.src_port_id(),
            src_channel = %relay_path.src_channel_id(),
            dst_chain = %relay_path.dst_chain().id(),
        )
    };

    // This Cache will store the IncentivizedPacket observed. They will then be used in order
    // to verify if a SendPacket event is incentivized.
    let incentivized_recv_cache: RwArc<Cache<Sequence, IncentivizedPacket>> = RwArc::new_lock(
        moka::sync::Cache::builder()
            .time_to_live(INCENTIVIZED_CACHE_TTL)
            .max_capacity(INCENTIVIZED_CACHE_MAX_CAPACITY)
            .build(),
    );

    spawn_background_task(span, Some(Duration::from_millis(200)), move || {
        if let Ok(cmd) = cmd_rx.try_recv() {
            handle_incentivized_packet_cmd(
                &mut link.lock().unwrap(),
                &path,
                cmd,
                &incentivized_recv_cache,
                &fee_filter,
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

/// Receives incentivized worker commands and handles them accordingly.
///
/// Given an `IbcEvent` command, filters the SendPacket and WriteAcknowledgment
/// events using the FeesFilters and updates the schedule.
///
/// The incentivized worker does not clear packet, so it only looks for
/// `IbcEvent` commands.
///
/// Regardless of the incoming command, this method also refreshes and
/// and executes any scheduled operational data that is ready.
fn handle_incentivized_packet_cmd<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    path: &Packet,
    cmd: WorkerCmd,
    incentivized_recv_cache: &RwArc<Cache<Sequence, IncentivizedPacket>>,
    fee_filter: &FeePolicy,
) -> Result<(), TaskError<RunError>> {
    // Handle command-specific task
    if let WorkerCmd::IbcEvents { mut batch } = cmd {
        // Iterate through the batch in order to retrieve the IncentivizedPacket
        // which will be used to confirm if a SendPacket event is incentivized.
        for event in batch.events.clone() {
            if let IbcEvent::IncentivizedPacket(packet) = event.event {
                incentivized_recv_cache
                    .acquire_write()
                    .insert(packet.sequence, packet.clone());
            }
            // It is not authorized to filter WriteAcknowledgement at the moment.
            // This is because in order to filter them the worker would need to
            // query the IncentivizedPacket events seen by the worker handling packets
            // from ChainB to ChainA or it would need to query ChainA for incentivized
            // packets.
            // In addition if the WriteAcknowledgment are not relayed, no fees will be paid.
            //IbcEvent::WriteAcknowledgement(ack) => get_incentivized_for_write_acknowledgement(link, ack, event.height.revision_height(), incentivized_ack_cache.clone()),
        }
        filter_batch(batch.borrow_mut(), incentivized_recv_cache, fee_filter);
        handle_update_schedule(link, 0, path, batch)
    } else {
        Ok(())
    }
}

/// It is only possible to filter incentivized packets using the `recv_fee` as criteria.
/// This method is a helper which can be used if filtering using `ack_fee` is added.
/// It queries the chain for incentivized packet information regarding the `WriteAcknowledgement`,
/// and stores this information in a Read/Write Cache.
fn _get_incentivized_for_write_acknowledgement<ChainA: ChainHandle, ChainB: ChainHandle>(
    link: &mut Link<ChainA, ChainB>,
    ack: WriteAcknowledgement,
    height: u64,
    incentivized_ack_cache: RwArc<Cache<Sequence, IdentifiedPacketFees>>,
) {
    let dst_chain = link.a_to_b.dst_chain();

    // Build PacketId required for the QueryIncentivizedPacketRequest
    let packet_id = PacketId {
        port_id: ack.packet.source_port.to_string(),
        channel_id: ack.packet.source_channel.to_string(),
        sequence: ack.packet.sequence.into(),
    };

    let request = QueryIncentivizedPacketRequest {
        packet_id: Some(packet_id),
        query_height: height,
    };

    match dst_chain.query_incentivized_packet(request) {
        Ok(ev) => {
            if let Some(identifier_packet_fees) = ev.incentivized_packet {
                if let Some(packet) = &identifier_packet_fees.packet_id {
                    incentivized_ack_cache
                        .acquire_write()
                        .insert(packet.sequence.into(), identifier_packet_fees);
                }
            }
        }
        // If the query failed it could mean that the packet is not incentivized.
        // The error is logged as debug.
        Err(e) => {
            debug!("Query for incentivized packet failed: {e}");
        }
    }
}

/// Using the configured FeesFilter and observed/queried information for
/// incentivized packets, determine if the SendPacket and WriteAcknowledgement events
/// should be relayed or not.
fn filter_batch(
    batch: &mut EventBatch,
    incentivized_recv_cache: &RwArc<Cache<Sequence, IncentivizedPacket>>,
    fee_filter: &FeePolicy,
) {
    batch.events.retain(|e| match &e.event {
        IbcEvent::SendPacket(packet) => incentivized_recv_cache
            .acquire_read()
            .get(&packet.packet.sequence)
            .map_or(false, |incentivized_event| {
                let grouped_amounts =
                    retrieve_all_fees_from_incentivized_packet(incentivized_event);

                fee_filter.should_relay(IbcEventType::SendPacket, &grouped_amounts)
            }),
        _ => true,
    });
}

/// Multiple fees with different denoms can be specified as rewards,
/// in an `IncentivizedPacket`. This method extract all and groups all
/// the fees with the same denom.
fn retrieve_all_fees_from_incentivized_packet(
    incentivized_packet: IncentivizedPacket,
) -> Vec<RawCoin> {
    incentivized_packet
        .total_recv_fee
        .iter()
        .group_by(|a| &a.denom)
        .into_iter()
        .map(|(key, group)| {
            let total_amount: Amount = group.map(|v| v.amount).sum::<Amount>();
            Coin::new(key.to_owned(), total_amount)
        })
        .collect()
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
    use ibc_relayer_types::events::IbcEvent::WriteAcknowledgement;

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
    use ibc_relayer_types::events::IbcEvent::AcknowledgePacket;

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
    use ibc_relayer_types::events::IbcEvent::TimeoutPacket;
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
