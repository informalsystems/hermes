use core::time::Duration;
use crossbeam_channel::Receiver;
use tracing::{debug, error_span};

use crate::connection::Connection as RelayConnection;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    object::Connection,
    util::retry::retry_with_index,
    worker::retry_strategy,
};

use super::error::RunError;
use super::WorkerCmd;

pub fn spawn_connection_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    connection: Connection,
    chains: ChainHandlePair<ChainA, ChainB>,
    cmd_rx: Receiver<WorkerCmd>,
) -> TaskHandle {
    spawn_background_task(
        error_span!("connection", connection = %connection.short_name()),
        Some(Duration::from_millis(200)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // there can be up to two event for this connection, e.g. init and try.
                        // process the last event, the one with highest "rank".
                        let last_event = batch.events.last();

                        debug!("starts processing {:#?}", last_event);

                        if let Some(event) = last_event {
                            let mut handshake_connection = RelayConnection::restore_from_event(
                                chains.a.clone(),
                                chains.b.clone(),
                                event.clone(),
                            )
                            .map_err(|e| TaskError::Fatal(RunError::connection(e)))?;

                            retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                                handshake_connection.step_event(event.clone(), index)
                            })
                            .map_err(|e| TaskError::Fatal(RunError::retry(e)))
                        } else {
                            Ok(Next::Continue)
                        }
                    }

                    WorkerCmd::NewBlock {
                        height: current_height,
                        new_block: _,
                    } => {
                        debug!("starts processing block event at {}", current_height);

                        let height = current_height
                            .decrement()
                            .map_err(|e| TaskError::Fatal(RunError::ics02(e)))?;

                        let (mut handshake_connection, state) =
                            RelayConnection::restore_from_state(
                                chains.a.clone(),
                                chains.b.clone(),
                                connection.clone(),
                                height,
                            )
                            .map_err(|e| TaskError::Fatal(RunError::connection(e)))?;

                        retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                            handshake_connection.step_state(state, index)
                        })
                        .map_err(|e| TaskError::Fatal(RunError::retry(e)))
                    }

                    // nothing to do
                    WorkerCmd::ClearPendingPackets => Ok(Next::Continue),
                }
            } else {
                Ok(Next::Continue)
            }
        },
    )
}
