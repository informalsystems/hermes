use core::time::Duration;
use crossbeam_channel::Receiver;
use tracing::{debug, warn};

use crate::channel::Channel as RelayChannel;
use crate::util::task::{spawn_background_task, TaskError, TaskHandle};
use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    object::Channel,
    util::retry::retry_with_index,
    worker::retry_strategy,
};

use super::error::RunError;
use super::WorkerCmd;

pub fn spawn_channel_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    channel: Channel,
    chains: ChainHandlePair<ChainA, ChainB>,
    cmd_rx: Receiver<WorkerCmd>,
) -> TaskHandle {
    let mut resume_handshake = true;

    spawn_background_task(
        "channel_worker".to_string(),
        Some(Duration::from_millis(200)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                let result = match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // there can be up to two event for this channel, e.g. init and try.
                        // process the last event, the one with highest "rank".
                        let last_event = batch.events.last();
                        debug!(
                            channel = %channel.short_name(),
                            "channel worker starts processing {:#?}", last_event
                        );

                        match last_event {
                            Some(event) => {
                                let mut handshake_channel = RelayChannel::restore_from_event(
                                    chains.a.clone(),
                                    chains.b.clone(),
                                    event.clone(),
                                )
                                .map_err(|e| TaskError::Fatal(RunError::channel(e)))?;

                                retry_with_index(
                                    retry_strategy::worker_default_strategy(),
                                    |index| handshake_channel.step_event(event.clone(), index),
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
                            channel = %channel.short_name(),
                            "Channel worker starts processing block event at {:#?}", current_height
                        );

                        let height = current_height
                            .decrement()
                            .map_err(|e| TaskError::Fatal(RunError::ics02(e)))?;

                        let (mut handshake_channel, state) = RelayChannel::restore_from_state(
                            chains.a.clone(),
                            chains.b.clone(),
                            channel.clone(),
                            height,
                        )
                        .map_err(|e| TaskError::Fatal(RunError::channel(e)))?;

                        retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                            handshake_channel.step_state(state, index)
                        })
                    }

                    WorkerCmd::ClearPendingPackets => Ok(()), // nothing to do
                };

                if let Err(retries) = result {
                    warn!(channel = %channel.short_name(), "Channel worker failed after {} retries", retries);

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
