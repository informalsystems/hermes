use core::convert::Infallible;
use core::time::Duration;
use crossbeam_channel::Receiver;
use retry::delay::Fibonacci;
use retry::retry_with_index;
use std::time::Instant;
use tracing::{debug, debug_span, error_span, trace, warn};

use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::events::IbcEvent;

use crate::util::retry::clamp_total;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::{
    chain::handle::ChainHandle,
    foreign_client::{ForeignClient, MisbehaviourResults},
};

use super::WorkerCmd;

const REFRESH_INTERVAL: Duration = Duration::from_secs(2); // 2 seconds
const INITIAL_BACKOFF: Duration = Duration::from_secs(1); // 1 second
const MAX_REFRESH_DELAY: Duration = Duration::from_secs(60 * 60); // 1 hour
const MAX_REFRESH_TOTAL_DELAY: Duration = Duration::from_secs(60 * 60 * 24); // 1 day

pub fn spawn_refresh_client<ChainA: ChainHandle, ChainB: ChainHandle>(
    mut client: ForeignClient<ChainA, ChainB>,
) -> Option<TaskHandle> {
    if client.is_expired_or_frozen() {
        warn!(
            client = %client.id,
            "skipping refresh client task on frozen client",
        );

        return None;
    }

    // Compute the refresh interval as a fraction of the client's trusting period
    // If the trusting period or the client state is not retrieved, fallback to a default value.
    let mut next_refresh = Instant::now() + REFRESH_INTERVAL;
    Some(spawn_background_task(
        error_span!(
            "worker.client.refresh",
            client = %client.id,
            src_chain = %client.src_chain.id(),
            dst_chain = %client.dst_chain.id(),
        ),
        Some(Duration::from_secs(1)),
        move || {
            // This is used for integration tests until `spawn_background_task`
            // uses async instead of threads
            if Instant::now() < next_refresh {
                return Ok(Next::Continue);
            }

            // Use retry mechanism only if `client.refresh()` fails.
            let res = retry_with_index(refresh_strategy(), |_| client.refresh());

            match res {
                // If `client.refresh()` was successful, update the `next_refresh` call.
                Ok(_) => {
                    next_refresh = Instant::now() + REFRESH_INTERVAL;

                    Ok(Next::Continue)
                }
                // If `client.refresh()` failed and the retry mechanism
                // exceeded the maximum delay, return a fatal error.
                Err(e) => Err(TaskError::Fatal(e)),
            }
        },
    ))
}

pub fn detect_misbehavior_task<ChainA: ChainHandle, ChainB: ChainHandle>(
    receiver: Receiver<WorkerCmd>,
    client: ForeignClient<ChainB, ChainA>,
) -> Option<TaskHandle> {
    if client.is_expired_or_frozen() {
        warn!(
            client = %client.id(),
            src_chain = %client.src_chain.id(),
            dst_chain = %client.dst_chain.id(),
            "skipping detect misbehavior task on frozen client",
        );

        return None;
    }

    let mut initial_check_done = false;

    let handle = spawn_background_task(
        error_span!(
            "worker.client.misbehaviour",
            client = %client.id,
            src_chain = %client.src_chain.id(),
            dst_chain = %client.dst_chain.id(),
        ),
        Some(Duration::from_millis(600)),
        move || -> Result<Next, TaskError<Infallible>> {
            if !initial_check_done {
                initial_check_done = true;

                debug!("doing initial misbehavior check");
                let result = client.detect_misbehaviour_and_submit_evidence(None);
                debug!("misbehavior detection result: {:?}", result);
            }

            if let Ok(WorkerCmd::IbcEvents { batch }) = receiver.try_recv() {
                trace!("received batch: {:?}", batch);

                for event_with_height in batch.events {
                    if let IbcEvent::UpdateClient(update) = event_with_height.event {
                        match on_client_update(&client, update) {
                            Next::Continue => continue,
                            Next::Abort => return Ok(Next::Abort),
                        }
                    }
                }
            }

            Ok(Next::Continue)
        },
    );

    Some(handle)
}

fn on_client_update<ChainA: ChainHandle, ChainB: ChainHandle>(
    client: &ForeignClient<ChainB, ChainA>,
    update: UpdateClient,
) -> Next {
    let _span = debug_span!(
        "on_client_update",
        client = %update.client_id(),
        client_type = %update.client_type(),
        height = %update.consensus_height(),
    );

    debug!("checking misbehavior for updated client");

    let result = client.detect_misbehaviour_and_submit_evidence(Some(update));

    trace!("misbehavior detection result: {:?}", result);

    match result {
        MisbehaviourResults::ValidClient => {
            debug!("client is valid");

            Next::Continue
        }
        MisbehaviourResults::VerificationError => {
            // can retry in next call
            debug!("client verification error, will retry in next call");

            Next::Continue
        }
        MisbehaviourResults::EvidenceSubmitted(_) => {
            // if evidence was submitted successfully then exit
            debug!("misbehavior detected! Evidence successfully submitted, exiting");

            Next::Abort
        }
        MisbehaviourResults::CannotExecute => {
            // skip misbehaviour checking if chain does not have support for it (i.e. client
            // update event does not include the header)
            debug!("cannot execute misbehavior detection, exiting");

            Next::Abort
        }
    }
}

fn refresh_strategy() -> impl Iterator<Item = Duration> {
    clamp_total(
        Fibonacci::from(INITIAL_BACKOFF),
        MAX_REFRESH_DELAY,
        MAX_REFRESH_TOTAL_DELAY,
    )
}
