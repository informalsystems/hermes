use std::time::Duration;

use anomaly::BoxError;
use crossbeam_channel::Receiver;
use tracing::{error, info, warn};

use crate::{
    chain::handle::ChainHandlePair,
    link::{Link, LinkParameters, RelaySummary},
    object::Packet,
    telemetry,
    telemetry::Telemetry,
    util::retry::{retry_with_index, RetryResult},
    worker::retry_strategy,
};

use super::WorkerCmd;

enum Step {
    Success(RelaySummary),
    Shutdown,
}

#[derive(Debug)]
pub struct PacketWorker {
    path: Packet,
    chains: ChainHandlePair,
    cmd_rx: Receiver<WorkerCmd>,
    telemetry: Telemetry,
    clear_packets_interval: u64,
}

impl PacketWorker {
    pub fn new(
        path: Packet,
        chains: ChainHandlePair,
        cmd_rx: Receiver<WorkerCmd>,
        telemetry: Telemetry,
        clear_packets_interval: u64,
    ) -> Self {
        Self {
            path,
            chains,
            cmd_rx,
            telemetry,
            clear_packets_interval,
        }
    }

    /// Run the event loop for events associated with a [`Packet`].
    pub fn run(self) -> Result<(), BoxError> {
        let mut link = Link::new_from_opts(
            self.chains.a.clone(),
            self.chains.b.clone(),
            LinkParameters {
                src_port_id: self.path.src_port_id.clone(),
                src_channel_id: self.path.src_channel_id.clone(),
            },
        )?;

        // TODO: Do periodical checks that the link is closed (upon every retry in the loop).
        if link.is_closed()? {
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

            let result = retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                self.step(maybe_cmd.clone(), &mut link, index)
            });

            match result {
                Ok(Step::Success(_summary)) => {
                    telemetry!(self.packet_metrics(&_summary));
                }

                Ok(Step::Shutdown) => {
                    info!(path = %self.path.short_name(), "shutting down Packet worker");
                    return Ok(());
                }

                Err(retries) => {
                    return Err(format!("Packet worker failed after {} retries", retries).into());
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
    fn step(&self, cmd: Option<WorkerCmd>, link: &mut Link, index: u64) -> RetryResult<Step, u64> {
        if let Some(cmd) = cmd {
            let result = match cmd {
                WorkerCmd::IbcEvents { batch } => link.a_to_b.update_schedule(batch),

                // Handle the arrival of an event signaling that the
                // source chain has advanced to a new block.
                WorkerCmd::NewBlock {
                    height,
                    new_block: _,
                } => {
                    // Schedule the clearing of pending packets. This should happen
                    // once at start, and _forced_ at predefined block intervals.
                    let force_packet_clearing = self.clear_packets_interval != 0
                        && height.revision_height % self.clear_packets_interval == 0;
                    link.a_to_b
                        .schedule_packet_clearing(height, force_packet_clearing)
                }

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

        let result = link
            .a_to_b
            .refresh_schedule()
            .and_then(|_| link.a_to_b.execute_schedule());

        match result {
            Ok(summary) => RetryResult::Ok(Step::Success(summary)),
            Err(e) => {
                error!(
                    path = %self.path.short_name(),
                    "[{}] worker: schedule execution encountered error: {}",
                    link.a_to_b, e
                );

                RetryResult::Retry(index)
            }
        }
    }

    /// Get a reference to the uni chan path worker's chains.
    pub fn chains(&self) -> &ChainHandlePair {
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

        self.telemetry.ibc_receive_packets(
            &self.path.src_chain_id,
            &self.path.src_channel_id,
            &self.path.src_port_id,
            count as u64,
        )
    }

    #[cfg(feature = "telemetry")]
    fn acknowledgment_metrics(&self, summary: &RelaySummary) {
        use ibc::events::IbcEvent::AcknowledgePacket;

        let count = summary
            .events
            .iter()
            .filter(|e| matches!(e, AcknowledgePacket(_)))
            .count();

        self.telemetry.ibc_acknowledgment_packets(
            &self.path.src_chain_id,
            &self.path.src_channel_id,
            &self.path.src_port_id,
            count as u64,
        )
    }

    #[cfg(feature = "telemetry")]
    fn timeout_metrics(&self, summary: &RelaySummary) {
        use ibc::events::IbcEvent::TimeoutPacket;
        let count = summary
            .events
            .iter()
            .filter(|e| matches!(e, TimeoutPacket(_)))
            .count();

        self.telemetry.ibc_timeout_packets(
            &self.path.src_chain_id,
            &self.path.src_channel_id,
            &self.path.src_port_id,
            count as u64,
        )
    }
}
