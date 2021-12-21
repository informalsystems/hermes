use core::time::Duration;

use crossbeam_channel::{Receiver, TryRecvError};
use tracing::{debug, trace};

use ibc::events::IbcEvent;

use crate::util::task::{spawn_background_task, TaskError, TaskHandle};
use crate::{
    chain::handle::ChainHandle,
    foreign_client::{
        ForeignClient, ForeignClientError, ForeignClientErrorDetail, MisbehaviourResults,
    },
    telemetry,
};

use super::WorkerCmd;

pub fn spawn_refresh_client<ChainA: ChainHandle + 'static, ChainB: ChainHandle + 'static>(
    mut client: ForeignClient<ChainA, ChainB>,
) -> TaskHandle {
    spawn_background_task(
        format!("RefreshClientWorker({})", client),
        Some(Duration::from_secs(1)),
        move || -> Result<(), TaskError<ForeignClientError>> {
            let res = client.refresh().map_err(|e| {
                if let ForeignClientErrorDetail::ExpiredOrFrozen(_) = e.detail() {
                    TaskError::Fatal(e)
                } else {
                    TaskError::Ignore(e)
                }
            })?;

            if res.is_some() {
                telemetry!(ibc_client_updates, &client.dst_chain.id(), &client.id, 1);
            }

            Ok(())
        },
    )
}

pub fn detect_misbehavior_task<ChainA: ChainHandle + 'static, ChainB: ChainHandle + 'static>(
    receiver: Receiver<WorkerCmd>,
    client: ForeignClient<ChainB, ChainA>,
) -> Option<TaskHandle> {
    match client.detect_misbehaviour_and_submit_evidence(None) {
        MisbehaviourResults::ValidClient => {}
        MisbehaviourResults::VerificationError => {}
        MisbehaviourResults::EvidenceSubmitted(_) => {
            return None;
        }
        MisbehaviourResults::CannotExecute => {
            return None;
        }
    }

    let handle = spawn_background_task(
        format!("DetectMisbehaviorWorker({})", client),
        Some(Duration::from_millis(600)),
        move || -> Result<(), TaskError<TryRecvError>> {
            if let Ok(cmd) = receiver.try_recv() {
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        trace!("[{}] worker received batch: {:?}", client, batch);

                        for event in batch.events {
                            if let IbcEvent::UpdateClient(update) = event {
                                debug!("[{}] client was updated", client);

                                match client.detect_misbehaviour_and_submit_evidence(Some(update)) {
                                    MisbehaviourResults::ValidClient => {}
                                    MisbehaviourResults::VerificationError => {
                                        // can retry in next call
                                    }
                                    MisbehaviourResults::EvidenceSubmitted(_) => {
                                        // if evidence was submitted successfully then exit
                                        return Err(TaskError::Abort);
                                    }
                                    MisbehaviourResults::CannotExecute => {
                                        // skip misbehaviour checking if chain does not have support for it (i.e. client
                                        // update event does not include the header)
                                        return Err(TaskError::Abort);
                                    }
                                }
                            }
                        }
                    }

                    WorkerCmd::NewBlock { .. } => {}
                    WorkerCmd::ClearPendingPackets => {}
                }
            }

            Ok(())
        },
    );

    Some(handle)
}
