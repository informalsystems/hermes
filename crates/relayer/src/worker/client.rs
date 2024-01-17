use core::{
    convert::Infallible,
    time::Duration,
};

use crossbeam_channel::Receiver;
use ibc_relayer_types::{
    core::ics02_client::events::UpdateClient,
    events::IbcEvent,
};
use retry::{
    delay::Fibonacci,
    retry_with_index,
};
use tracing::{
    debug,
    debug_span,
    error_span,
    trace,
    warn,
};

use super::WorkerCmd;
use crate::{
    chain::handle::ChainHandle,
    foreign_client::{
        ForeignClient,
        MisbehaviourResults,
    },
    util::{
        retry::clamp_total,
        task::{
            spawn_background_task,
            Next,
            TaskError,
            TaskHandle,
        },
    },
};

const REFRESH_CHECK_INTERVAL: Duration = Duration::from_secs(5); // 5 seconds
const INITIAL_BACKOFF: Duration = Duration::from_secs(5); // 5 seconds
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

    Some(spawn_background_task(
        error_span!(
            "worker.client.refresh",
            client = %client.id,
            src_chain = %client.src_chain.id(),
            dst_chain = %client.dst_chain.id(),
        ),
        Some(REFRESH_CHECK_INTERVAL),
        move || {
            // Try to refresh the client, but only if the refresh window has expired.
            // If the refresh fails, retry according to the given strategy.
            let res = retry_with_index(refresh_strategy(), |_| client.refresh());

            match res {
                // If `client.refresh()` was successful, continue
                Ok(_) => Ok(Next::Continue),

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
