use core::time::Duration;

use crossbeam_channel::Receiver;
use ibc::Height;
use tracing::{error, info, trace, warn};

use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    config::Packets as PacketsConfig,
    link::{Link, LinkParameters, RelaySummary},
    object::Packet,
    telemetry,
    util::retry::{retry_with_index, RetryResult},
    worker::retry_strategy,
};

use super::error::RunError;
use super::WorkerCmd;

enum Step {
    Success(RelaySummary),
    Shutdown,
}

#[derive(Debug)]
pub struct PacketWorker<ChainA: ChainHandle, ChainB: ChainHandle> {
    path: Packet,
    chains: ChainHandlePair<ChainA, ChainB>,
    cmd_rx: Receiver<WorkerCmd>,
    packets_cfg: PacketsConfig,
    first_run: bool,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> PacketWorker<ChainA, ChainB> {
    pub fn new(
        path: Packet,
        chains: ChainHandlePair<ChainA, ChainB>,
        cmd_rx: Receiver<WorkerCmd>,
        packets_cfg: PacketsConfig,
    ) -> Self {
        Self {
            path,
            chains,
            cmd_rx,
            packets_cfg,
            first_run: true,
        }
    }

    /// Whether or not to clear pending packets at this `step` for the given height.
    /// Packets are cleared on the first iteration if `clear_on_start` is true.
    /// Subsequently, packets are cleared only if `clear_interval` is not `0` and
    /// if we have reached the interval.
    fn clear_packets(&mut self, height: Height) -> bool {
        if self.first_run {
            self.first_run = false;
            self.packets_cfg.clear_on_start
        } else {
            self.packets_cfg.clear_interval != 0
                && height.revision_height % self.packets_cfg.clear_interval == 0
        }
    }

    /// Run the event loop for events associated with a [`Packet`].
    pub fn run(mut self) -> Result<(), RunError> {
        let mut link = Link::new_from_opts(
            self.chains.a.clone(),
            self.chains.b.clone(),
            LinkParameters {
                src_port_id: self.path.src_port_id.clone(),
                src_channel_id: self.path.src_channel_id.clone(),
            },
            self.packets_cfg.tx_confirmation,
        )
        .map_err(RunError::link)?;

        let is_closed = link.is_closed().map_err(RunError::link)?;

        // TODO: Do periodical checks that the link is closed (upon every retry in the loop).
        if is_closed {
            warn!("channel is closed, exiting");
            return Ok(());
        }

        loop {
            const BACKOFF: Duration = Duration::from_millis(200);

            // Pop-out any unprocessed commands
            // If there are no incoming commands, it's safe to backoff.
            let maybe_cmd = crossbeam_channel::select! {
                recv(self.cmd_rx) -> cmd => cmd.ok(),
                recv(crossbeam_channel::after(BACKOFF)) -> _ => None,
            };

            let result = retry_with_index(retry_strategy::worker_stubborn_strategy(), |index| {
                self.step(maybe_cmd.clone(), &mut link, index)
            });

            match result {
                Ok(Step::Success(summary)) => {
                    if !summary.is_empty() {
                        trace!("Packet worker produced relay summary: {:?}", summary);
                    }
                    telemetry!(self.packet_metrics(&summary));
                }

                Ok(Step::Shutdown) => {
                    info!(path = %self.path.short_name(), "shutting down Packet worker");
                    return Ok(());
                }

                Err(retries) => {
                    return Err(RunError::retry(retries));
                }
            }
        }
    }

    /// Receives worker commands, which may be:
    ///     - IbcEvent => then it updates schedule
    ///     - NewBlock => schedules packet clearing
    ///     - Shutdown => exits
    ///
    /// Regardless of the incoming command, this method
    /// also refreshes and executes any scheduled operational
    /// data that is ready.
    fn step(
        &mut self,
        cmd: Option<WorkerCmd>,
        link: &mut Link<ChainA, ChainB>,
        index: u64,
    ) -> RetryResult<Step, u64> {
        if let Some(cmd) = cmd {
            let result = match cmd {
                WorkerCmd::IbcEvents { batch } => link.a_to_b.update_schedule(batch),

                // Handle the arrival of an event signaling that the
                // source chain has advanced to a new block.
                WorkerCmd::NewBlock {
                    height,
                    new_block: _,
                } => {
                    // Schedule the clearing of pending packets. This may happen once at start,
                    // and may be _forced_ at predefined block intervals.
                    link.a_to_b
                        .schedule_packet_clearing(Some(height), self.clear_packets(height))
                }

                WorkerCmd::ClearPendingPackets => link.a_to_b.schedule_packet_clearing(None, true),

                WorkerCmd::Shutdown => {
                    return RetryResult::Ok(Step::Shutdown);
                }
            };

            if let Err(e) = result {
                error!(
                    path = %self.path.short_name(),
                    "[{}] worker: handling command encountered error: {}",
                    link.a_to_b, e
                );

                return RetryResult::Retry(index);
            }
        }

        if let Err(e) = link
            .a_to_b
            .refresh_schedule()
            .and_then(|_| link.a_to_b.execute_schedule())
        {
            error!(
                "[{}] worker: schedule execution encountered error: {}",
                link.a_to_b, e
            );
            return RetryResult::Retry(index);
        }

        let confirmation_result = link.a_to_b.process_pending_txs();

        RetryResult::Ok(Step::Success(confirmation_result))
    }

    /// Get a reference to the uni chan path worker's chains.
    pub fn chains(&self) -> &ChainHandlePair<ChainA, ChainB> {
        &self.chains
    }

    /// Get a reference to the client worker's object.
    pub fn object(&self) -> &Packet {
        &self.path
    }

    #[cfg(feature = "telemetry")]
    fn packet_metrics(&self, summary: &RelaySummary) {
        self.receive_packet_metrics(summary);
        self.acknowledgment_metrics(summary);
        self.timeout_metrics(summary);
    }

    #[cfg(feature = "telemetry")]
    fn receive_packet_metrics(&self, summary: &RelaySummary) {
        use ibc::events::IbcEvent::WriteAcknowledgement;

        let count = summary
            .events
            .iter()
            .filter(|e| matches!(e, WriteAcknowledgement(_)))
            .count();

        telemetry!(
            ibc_receive_packets,
            &self.path.src_chain_id,
            &self.path.src_channel_id,
            &self.path.src_port_id,
            count as u64,
        );
    }

    #[cfg(feature = "telemetry")]
    fn acknowledgment_metrics(&self, summary: &RelaySummary) {
        use ibc::events::IbcEvent::AcknowledgePacket;

        let count = summary
            .events
            .iter()
            .filter(|e| matches!(e, AcknowledgePacket(_)))
            .count();

        telemetry!(
            ibc_acknowledgment_packets,
            &self.path.src_chain_id,
            &self.path.src_channel_id,
            &self.path.src_port_id,
            count as u64,
        );
    }

    #[cfg(feature = "telemetry")]
    fn timeout_metrics(&self, summary: &RelaySummary) {
        use ibc::events::IbcEvent::TimeoutPacket;
        let count = summary
            .events
            .iter()
            .filter(|e| matches!(e, TimeoutPacket(_)))
            .count();

        telemetry!(
            ibc_timeout_packets,
            &self.path.src_chain_id,
            &self.path.src_channel_id,
            &self.path.src_port_id,
            count as u64,
        );
    }
}
