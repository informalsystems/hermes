use core::time::Duration;
use crossbeam_channel::Receiver;
use tracing::debug;

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
    spawn_background_task(
        "channel_worker".to_string(),
        Some(Duration::from_millis(200)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // there can be up to two event for this channel, e.g. init and try.
                        // process the last event, the one with highest "rank".
                        let last_event = batch.events.last();
                        debug!(
                            channel = %channel.short_name(),
                            "channel worker starts processing {:#?}", last_event
                        );

                        if let Some(event) = last_event {
                            let mut handshake_channel = RelayChannel::restore_from_event(
                                chains.a.clone(),
                                chains.b.clone(),
                                event.clone(),
                            )
                            .map_err(|e| TaskError::Fatal(RunError::channel(e)))?;

                            retry_with_index(retry_strategy::worker_default_strategy(), |index| {
                                handshake_channel.step_event(event.clone(), index)
                            })
                            .map_err(|e| TaskError::Fatal(RunError::retry(e)))?;
                        }
                    }
                    WorkerCmd::NewBlock {
                        height: current_height,
                        new_block: _,
                    } => {
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
                        .map_err(|e| TaskError::Fatal(RunError::retry(e)))?;
                    }

                    WorkerCmd::ClearPendingPackets => {} // nothing to do
                };
            }

            Ok(())
        },
    )
}
