use std::{thread, time::Duration};

use anomaly::BoxError;
use crossbeam_channel::Receiver;
use tracing::{error, warn};

use crate::{
    chain::handle::ChainHandlePair,
    link::{Link, LinkParameters},
    object::UnidirectionalChannelPath,
    util::retry::{retry_with_index, RetryResult},
};

use super::WorkerCmd;

mod retry_strategy {
    use crate::util::retry::{clamp_total, ConstantGrowth};
    use std::time::Duration;

    const MAX_DELAY: Duration = Duration::from_millis(500);
    const DELAY_INCR: Duration = Duration::from_millis(100);
    const INITIAL_DELAY: Duration = Duration::from_millis(200);
    const MAX_RETRY_DURATION: Duration = Duration::from_secs(2);

    pub fn default() -> impl Iterator<Item = Duration> {
        let strategy = ConstantGrowth::new(INITIAL_DELAY, DELAY_INCR);
        clamp_total(strategy, MAX_DELAY, MAX_RETRY_DURATION)
    }
}

pub struct UniChanPathWorker {
    chains: ChainHandlePair,
    rx: Receiver<WorkerCmd>,
    path: UnidirectionalChannelPath,
}

impl UniChanPathWorker {
    pub fn new(
        chains: ChainHandlePair,
        rx: Receiver<WorkerCmd>,
        path: UnidirectionalChannelPath,
    ) -> Self {
        Self { chains, rx, path }
    }

    /// Run the event loop for events associated with a [`UnidirectionalChannelPath`].
    pub fn run(self) -> Result<(), BoxError> {
        let rx = self.rx;

        let mut link = Link::new_from_opts(
            self.chains.a.clone(),
            self.chains.b.clone(),
            LinkParameters {
                src_port_id: self.path.src_port_id,
                src_channel_id: self.path.src_channel_id,
            },
        )?;

        // TODO: Do periodical checks that the link is closed (upon every retry in the loop).
        if link.is_closed()? {
            warn!("channel is closed, exiting");
            return Ok(());
        }

        loop {
            thread::sleep(Duration::from_millis(200));

            let result = retry_with_index(retry_strategy::default(), |index| {
                Self::step(rx.try_recv().ok(), &mut link, index)
            });

            if let Err(retries) = result {
                return Err(format!(
                    "UnidirectionalChannelPath worker failed after {} retries",
                    retries
                )
                .into());
            }
        }
    }

    fn step(cmd: Option<WorkerCmd>, link: &mut Link, index: u64) -> RetryResult<(), u64> {
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

        if let Err(e) = result {
            error!("{}", e);
            return RetryResult::Retry(index);
        }

        RetryResult::Ok(())
    }

    /// Get a reference to the uni chan path worker's chains.
    pub fn chains(&self) -> &ChainHandlePair {
        &self.chains
    }
}
