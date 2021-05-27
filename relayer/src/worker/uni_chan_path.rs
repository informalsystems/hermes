use std::{thread, time::Duration};

use anomaly::BoxError;
use crossbeam_channel::Receiver;
use ibc::events::IbcEvent;
use tracing::{error, warn};

use crate::{
    chain::handle::ChainHandlePair,
    link::{Link, LinkParameters, RelaySummary},
    metric,
    object::UnidirectionalChannelPath,
    telemetry::TelemetryHandle,
    util::retry::{retry_with_index, RetryResult},
    worker::retry_strategy,
};

use super::WorkerCmd;

#[derive(Debug)]
pub struct UniChanPathWorker {
    path: UnidirectionalChannelPath,
    chains: ChainHandlePair,
    cmd_rx: Receiver<WorkerCmd>,
    telemetry: TelemetryHandle,
}

impl UniChanPathWorker {
    pub fn new(
        path: UnidirectionalChannelPath,
        chains: ChainHandlePair,
        cmd_rx: Receiver<WorkerCmd>,
        telemetry: TelemetryHandle,
    ) -> Self {
        Self {
            path,
            chains,
            cmd_rx,
            telemetry,
        }
    }

    /// Run the event loop for events associated with a [`UnidirectionalChannelPath`].
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
            thread::sleep(Duration::from_millis(200));

            let result = retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                Self::step(self.cmd_rx.try_recv().ok(), &mut link, index)
            });

            match result {
                Ok(summary) => {
                    metric!(self.telemetry, self.receive_packet_metric(&summary));
                }

                Err(retries) => {
                    return Err(format!(
                        "UnidirectionalChannelPath worker failed after {} retries",
                        retries
                    )
                    .into());
                }
            }
        }
    }

    fn step(cmd: Option<WorkerCmd>, link: &mut Link, index: u64) -> RetryResult<RelaySummary, u64> {
        if let Some(cmd) = cmd {
            let result = match cmd {
                WorkerCmd::IbcEvents { batch } => {
                    // Update scheduled batches.
                    link.a_to_b.update_schedule(batch)
                }
                WorkerCmd::NewBlock {
                    height,
                    new_block: _,
                } => link.a_to_b.clear_packets(height),
            };

            if let Err(e) = result {
                error!("{}", e);
                return RetryResult::Retry(index);
            }
        }

        let result = link
            .a_to_b
            .refresh_schedule()
            .and_then(|_| link.a_to_b.execute_schedule());

        match result {
            Ok(summary) => RetryResult::Ok(summary),
            Err(e) => {
                error!("{}", e);
                RetryResult::Retry(index)
            }
        }
    }

    /// Get a reference to the uni chan path worker's chains.
    pub fn chains(&self) -> &ChainHandlePair {
        &self.chains
    }

    /// Get a reference to the client worker's object.
    pub fn object(&self) -> &UnidirectionalChannelPath {
        &self.path
    }

    #[cfg(feature = "telemetry")]
    fn receive_packet_metric(&self, summary: &RelaySummary) -> ibc_telemetry::MetricUpdate {
        let count = summary
            .events
            .iter()
            .filter(|e| matches!(e, IbcEvent::WriteAcknowledgement(_)))
            .count();

        ibc_telemetry::MetricUpdate::IbcReceivePacket(
            self.path.src_chain_id.clone(),
            self.path.src_channel_id.clone(),
            self.path.src_port_id.clone(),
            count as u64,
        )
    }
}
