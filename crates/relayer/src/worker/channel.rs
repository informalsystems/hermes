use core::time::Duration;
use crossbeam_channel::Receiver;
use tracing::{debug, error_span};

use crate::channel::Channel as RelayChannel;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
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
    let mut complete_handshake_on_new_block = true;
    spawn_background_task(
        error_span!("worker.channel", channel = %channel.short_name()),
        Some(Duration::from_millis(200)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // there can be up to two event for this channel, e.g. init and try.
                        // process the last event, the one with highest "rank".
                        let last_event = batch.events.last();
                        debug!("starts processing {:?}", last_event);

                        complete_handshake_on_new_block = false;
                        if let Some(event_with_height) = last_event {
                            let mut handshake_channel = RelayChannel::restore_from_event(
                                chains.a.clone(),
                                chains.b.clone(),
                                event_with_height.event.clone(),
                            )
                            .map_err(|e| TaskError::Fatal(RunError::channel(e)))?;

                            retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                                handshake_channel.step_event(&event_with_height.event, index)
                            })
                            .map_err(|e| TaskError::Fatal(RunError::retry(e)))
                        } else {
                            Ok(Next::Continue)
                        }
                    }

                    WorkerCmd::NewBlock {
                        height: current_height,
                        new_block: _,
                    } if complete_handshake_on_new_block => {
                        debug!("starts processing block event at {:#?}", current_height);

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

                        complete_handshake_on_new_block = false;
                        retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                            handshake_channel.step_state(state, index)
                        })
                        .map_err(|e| TaskError::Fatal(RunError::retry(e)))
                    }

                    // nothing to do
                    _ => Ok(Next::Continue),
                }
            } else {
                Ok(Next::Continue)
            }
        },
    )
}
