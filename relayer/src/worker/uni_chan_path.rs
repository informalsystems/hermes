use std::{thread, time::Duration};

use crossbeam_channel::Receiver;
use tracing::{error, warn};

use crate::{
    chain::handle::ChainHandlePair,
    link::{Link, LinkParameters, RelaySummary},
    object::UnidirectionalChannelPath,
    telemetry,
    telemetry::Telemetry,
    util::retry::{retry_with_index, RetryResult},
    worker::retry_strategy,
};

use super::WorkerCmd;

#[derive(Debug)]
pub struct UniChanPathWorker {
    path: UnidirectionalChannelPath,
    chains: ChainHandlePair,
    cmd_rx: Receiver<WorkerCmd>,
    telemetry: Telemetry,
}

impl UniChanPathWorker {
    pub fn new(
        path: UnidirectionalChannelPath,
        chains: ChainHandlePair,
        cmd_rx: Receiver<WorkerCmd>,
        telemetry: Telemetry,
    ) -> Self {
        Self {
            path,
            chains,
            cmd_rx,
            telemetry,
        }
    }

    /// Run the event loop for events associated with a [`UnidirectionalChannelPath`].
    pub fn run(self) -> Result<(), Box<dyn std::error::Error>> {
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
                Ok(_summary) => {
                    telemetry!(self.packet_metrics(&_summary));
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
