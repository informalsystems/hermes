use std::{fmt, thread, time::Duration};

use anomaly::BoxError;
use crossbeam_channel::{Receiver, Sender};
use tracing::{debug, error, error_span, info, trace, warn};

use ibc::{events::IbcEvent, ics02_client::events::UpdateClient};

use crate::{
    chain::handle::ChainHandlePair,
    foreign_client::{ForeignClient, ForeignClientError, MisbehaviourResults},
    link::{Link, LinkParameters},
    object::{Client, Object, UnidirectionalChannelPath},
    util::retry::{retry_with_index, RetryResult},
};

mod handle;
pub use handle::WorkerHandle;

mod cmd;
pub use cmd::WorkerCmd;

mod retry_strategy {
    use crate::util::retry::{clamp_total, ConstantGrowth};
    use std::time::Duration;

    const MAX_DELAY: Duration = Duration::from_millis(500);
    const DELAY_INCR: Duration = Duration::from_millis(100);
    const INITIAL_DELAY: Duration = Duration::from_millis(200);
    const MAX_RETRY_DURATION: Duration = Duration::from_secs(2);

    pub fn uni_chan_path() -> impl Iterator<Item = Duration> {
        let strategy = ConstantGrowth::new(INITIAL_DELAY, DELAY_INCR);
        clamp_total(strategy, MAX_DELAY, MAX_RETRY_DURATION)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkerMsg {
    Stopped(Object),
}

/// A worker processes batches of events associated with a given [`Object`].
pub struct Worker {
    chains: ChainHandlePair,
    cmd_rx: Receiver<WorkerCmd>,
    msg_tx: Sender<WorkerMsg>,
}

impl fmt::Display for Worker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} <-> {}]", self.chains.a.id(), self.chains.b.id(),)
    }
}

impl Worker {
    /// Spawn a worker which relay events pertaining to an [`Object`] between two `chains`.
    pub fn spawn(
        chains: ChainHandlePair,
        object: Object,
        msg_tx: Sender<WorkerMsg>,
    ) -> WorkerHandle {
        let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();

        debug!(
            "[{}] spawned worker with chains a:{} and b:{} for object {:#?} ",
            object.short_name(),
            chains.a.id(),
            chains.b.id(),
            object,
        );

        let worker = Self {
            chains,
            cmd_rx,
            msg_tx,
        };

        let thread_handle = std::thread::spawn(move || worker.run(object));

        WorkerHandle::new(cmd_tx, thread_handle)
    }

    /// Run the worker event loop.
    fn run(self, object: Object) {
        let span = error_span!("worker loop", worker = %object.short_name());
        let _guard = span.enter();

        let msg_tx = self.msg_tx.clone();

        let result = match object.clone() {
            Object::UnidirectionalChannelPath(path) => self.run_uni_chan_path(path),
            Object::Client(client) => self.run_client(client),
        };

        if let Err(e) = result {
            error!("worker error: {}", e);
        }

        if let Err(e) = msg_tx.send(WorkerMsg::Stopped(object)) {
            error!("failed to notify supervisor that worker stopped: {}", e);
        }

        info!("worker stopped");
    }

    fn run_client_misbehaviour(
        &self,
        client: &ForeignClient,
        update: Option<UpdateClient>,
    ) -> bool {
        match client.detect_misbehaviour_and_submit_evidence(update) {
            MisbehaviourResults::ValidClient => false,
            MisbehaviourResults::VerificationError => {
                // can retry in next call
                false
            }
            MisbehaviourResults::EvidenceSubmitted(_) => {
                // if evidence was submitted successfully then exit
                true
            }
            MisbehaviourResults::CannotExecute => {
                // skip misbehaviour checking if chain does not have support for it (i.e. client
                // update event does not include the header)
                true
            }
        }
    }

    /// Run the event loop for events associated with a [`Client`].
    fn run_client(self, client: Client) -> Result<(), BoxError> {
        let mut client = ForeignClient::restore(
            &client.dst_client_id,
            self.chains.a.clone(),
            self.chains.b.clone(),
        );

        info!(
            "running client worker & initial misbehaviour detection for {}",
            client
        );

        // initial check for evidence of misbehaviour for all updates
        let skip_misbehaviour = self.run_client_misbehaviour(&client, None);

        info!(
            "running client worker (misbehaviour and refresh) for {}",
            client
        );

        loop {
            thread::sleep(Duration::from_millis(600));

            // Run client refresh, exit only if expired or frozen
            if let Err(e @ ForeignClientError::ExpiredOrFrozen(..)) = client.refresh() {
                error!("failed to refresh client '{}': {}", client, e);
                continue;
            }

            if skip_misbehaviour {
                continue;
            }

            if let Ok(WorkerCmd::IbcEvents { batch }) = self.cmd_rx.try_recv() {
                trace!("client '{}' worker receives batch {:?}", client, batch);

                for event in batch.events {
                    if let IbcEvent::UpdateClient(update) = event {
                        debug!("client '{}' updated", client);

                        // Run misbehaviour. If evidence submitted the loop will exit in next
                        // iteration with frozen client
                        self.run_client_misbehaviour(&client, Some(update));
                    }
                }
            }
        }
    }

    /// Run the event loop for events associated with a [`UnidirectionalChannelPath`].
    fn run_uni_chan_path(self, path: UnidirectionalChannelPath) -> Result<(), BoxError> {
        let mut link = Link::new_from_opts(
            self.chains.a.clone(),
            self.chains.b.clone(),
            LinkParameters {
                src_port_id: path.src_port_id,
                src_channel_id: path.src_channel_id,
            },
        )?;

        // TODO: Do periodical checks that the link is closed (upon every retry in the loop).
        if link.is_closed()? {
            warn!("channel is closed, exiting");
            return Ok(());
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

        loop {
            thread::sleep(Duration::from_millis(200));

            let result = retry_with_index(retry_strategy::uni_chan_path(), |index| {
                step(self.cmd_rx.try_recv().ok(), &mut link, index)
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
}
