use super::error::RunError;
use crate::object::CrossChainQuery;
use crate::util::task::{Next, spawn_background_task, TaskError, TaskHandle};
use crate::worker::WorkerCmd;
use crate::chain::handle::ChainHandle;
use crate::chain::requests::CrossChainQueryRequest;
use crate::chain::tracking::TrackedMsgs;

use std::time::Duration;
use crossbeam_channel::Receiver;
use tracing::{info, info_span};
use uuid::Uuid;

pub fn spawn_cross_chain_query_worker<ChainA: ChainHandle>(
    handle: ChainA,
    cmd_rx: Receiver<WorkerCmd>,
    cross_chain_query: CrossChainQuery,
)  -> TaskHandle {
    spawn_background_task(
        info_span!("cross_chain_query"),
        Some(Duration::from_millis(1000)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                handle_cross_chain_query(handle.clone(), cmd, &cross_chain_query)?;
            }
            Ok(Next::Continue)
        },
    )
}

fn handle_cross_chain_query<ChainA: ChainHandle>(
    handle: ChainA,
    cmd: WorkerCmd,
    _: &CrossChainQuery,
) -> Result<(), TaskError<RunError>> {
    if let WorkerCmd::IbcEvents {batch} = &cmd {
        let queries: Vec<CrossChainQueryRequest> = batch
            .events
            .iter()
            .filter_map(|ev| ev.try_into().ok())
            .collect();

        let response = handle.cross_chain_query(queries);
        if let Ok(res) = response {
            res.iter()
                .for_each(|r| info!("response arrived: query_id: {}", r.query_id));
            let any_msgs = res
                .clone()
                .into_iter()
                .map(|r| r.to_any(handle.get_signer().unwrap()))
                .collect::<Vec<_>>();

            handle
                .send_messages_and_wait_check_tx(TrackedMsgs::new_uuid(any_msgs, Uuid::new_v4()))
                .map_err(|_| TaskError::Ignore(RunError::query()))?;
        }
    }
    Ok(())
}