use core::convert::Infallible;
use core::time::Duration;
use crossbeam_channel::Receiver;
use tracing::{debug, trace, warn};

use ibc::events::IbcEvent;

use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::{
    chain::handle::ChainHandle,
    foreign_client::{ForeignClient, HasExpiredOrFrozenError, MisbehaviourResults},
    telemetry,
};

use super::WorkerCmd;

pub fn spawn_refresh_client<ChainA: ChainHandle, ChainB: ChainHandle>(
    mut client: ForeignClient<ChainA, ChainB>,
) -> Option<TaskHandle> {
    if client.is_expired_or_frozen() {
        warn!(
            "skipping refresh client task on frozen client: {}",
            client.id()
        );
        None
    } else {
        Some(spawn_background_task(
            format!("RefreshClientWorker({})", client),
            Some(Duration::from_secs(1)),
            move || {
                let res = client.refresh().map_err(|e| {
                    if e.is_expired_or_frozen_error() {
                        TaskError::Fatal(e)
                    } else {
                        TaskError::Ignore(e)
                    }
                })?;

                if res.is_some() {
                    telemetry!(ibc_client_updates, &client.dst_chain.id(), &client.id, 1);
                }

                Ok(Next::Continue)
            },
        ))
    }
}

pub fn detect_misbehavior_task<ChainA: ChainHandle, ChainB: ChainHandle>(
    receiver: Receiver<WorkerCmd>,
    client: ForeignClient<ChainB, ChainA>,
) -> Option<TaskHandle> {
    if client.is_expired_or_frozen() {
        warn!(
            "skipping detect misbehavior task on frozen client: {}",
            client.id()
        );
        return None;
    }

    {
        debug!("[{}] doing first misbehavior check", client);
        let misbehavior_result = client.detect_misbehaviour_and_submit_evidence(None);
        debug!(
            "[{}] detect misbehavior result: {:?}",
            client, misbehavior_result
        );
    }

    let handle = spawn_background_task(
        format!("DetectMisbehaviorWorker({})", client),
        Some(Duration::from_millis(600)),
        move || -> Result<Next, TaskError<Infallible>> {
            if let Ok(cmd) = receiver.try_recv() {
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        trace!("[{}] worker received batch: {:?}", client, batch);

                        for event in batch.events {
                            if let IbcEvent::UpdateClient(update) = event {
                                debug!("[{}] checking misbehavior for updated client", client);
                                let misbehavior_result =
                                    client.detect_misbehaviour_and_submit_evidence(Some(update));
                                trace!(
                                    "[{}] detect misbehavior result: {:?}",
                                    client,
                                    misbehavior_result
                                );

                                match misbehavior_result {
                                    MisbehaviourResults::ValidClient => {}
                                    MisbehaviourResults::VerificationError => {
                                        // can retry in next call
                                    }
                                    MisbehaviourResults::EvidenceSubmitted(_) => {
                                        // if evidence was submitted successfully then exit
                                        return Ok(Next::Abort);
                                    }
                                    MisbehaviourResults::CannotExecute => {
                                        // skip misbehaviour checking if chain does not have support for it (i.e. client
                                        // update event does not include the header)
                                        return Ok(Next::Abort);
                                    }
                                }
                            }
                        }
                    }

                    WorkerCmd::NewBlock { .. } => {}
                    WorkerCmd::ClearPendingPackets => {}
                }
            }

            Ok(Next::Continue)
        },
    );

    Some(handle)
}
