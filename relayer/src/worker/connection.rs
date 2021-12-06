use core::time::Duration;
use crossbeam_channel::Receiver;
use tracing::{debug, warn};

use crate::connection::Connection as RelayConnection;
use crate::util::task::{spawn_background_task, TaskError, TaskHandle};
use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    object::Connection,
    util::retry::retry_with_index,
    worker::retry_strategy,
};

use super::error::RunError;
use super::WorkerCmd;

pub fn spawn_connection_worker<ChainA: ChainHandle + 'static, ChainB: ChainHandle + 'static>(
    connection: Connection,
    chains: ChainHandlePair<ChainA, ChainB>,
    cmd_rx: Receiver<WorkerCmd>,
) -> TaskHandle {
    let mut resume_handshake = true;

    spawn_background_task(
        "connection_worker".to_string(),
        Some(Duration::from_millis(200)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                let result = match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // there can be up to two event for this connection, e.g. init and try.
                        // process the last event, the one with highest "rank".
                        let last_event = batch.events.last();

                        debug!(
                            connection = %connection.short_name(),
                            "connection worker starts processing {:#?}", last_event
                        );

                        match last_event {
                            Some(event) => {
                                let mut handshake_connection = RelayConnection::restore_from_event(
                                    chains.a.clone(),
                                    chains.b.clone(),
                                    event.clone(),
                                )
                                .map_err(|e| TaskError::Fatal(RunError::connection(e)))?;

                                retry_with_index(
                                    retry_strategy::worker_default_strategy(),
                                    |index| handshake_connection.step_event(event.clone(), index),
                                )
                            }
                            None => Ok(()),
                        }
                    }

                    WorkerCmd::NewBlock {
                        height: current_height,
                        new_block: _,
                    } => {
                        if !resume_handshake {
                            return Ok(());
                        }

                        debug!(
                            connection = %connection.short_name(),
                            "connection worker starts processing block event at {}",
                            current_height
                        );

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
                    }

                    WorkerCmd::ClearPendingPackets => Ok(()), // nothing to do
                };

                if let Err(retries) = result {
                    warn!(
                        connection = %connection.short_name(),
                        "connection worker failed after {} retries", retries
                    );

                    // Resume handshake on next iteration.
                    resume_handshake = true;
                } else {
                    resume_handshake = false;
                }
            }

            Ok(())
        },
    )
}
