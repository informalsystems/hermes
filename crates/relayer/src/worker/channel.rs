use core::time::Duration;
use crossbeam_channel::Receiver;
use ibc_relayer_types::events::IbcEventType;
use tracing::{debug, error_span, warn};

use crate::chain::requests::QueryHeight;
use crate::channel::{channel_handshake_retry, Channel as RelayChannel};
use crate::util::retry::RetryResult;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::{
    chain::handle::{ChainHandle, ChainHandlePair},
    object::Channel,
    util::retry::retry_with_index,
};

use super::error::RunError;
use super::WorkerCmd;

fn max_block_times<ChainA: ChainHandle, ChainB: ChainHandle>(
    chains: &ChainHandlePair<ChainA, ChainB>,
) -> Duration {
    let a_block_time = match chains.a.config() {
        Err(_e) => Duration::from_millis(500),
        Ok(config) => config.max_block_time(),
    };
    let b_block_time = match chains.b.config() {
        Err(_e) => Duration::from_millis(500),
        Ok(config) => config.max_block_time(),
    };
    a_block_time.max(b_block_time)
}

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
            let max_block_times = max_block_times(&chains);
            if let Ok(cmd) = cmd_rx.try_recv() {
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // there can be up to two event for this channel, e.g. init and try.
                        // process the last event, the one with highest "rank".
                        let last_event = batch.events.last();
                        debug!("starts processing {:?}", last_event);

                        complete_handshake_on_new_block = false;

                        if let Some(event_with_height) = last_event {
                            match event_with_height.event.event_type() {
                                IbcEventType::UpgradeInitChannel
                                | IbcEventType::UpgradeTryChannel
                                | IbcEventType::UpgradeAckChannel
                                | IbcEventType::UpgradeConfirmChannel
                                | IbcEventType::UpgradeOpenChannel
                                | IbcEventType::UpgradeTimeoutChannel => retry_with_index(
                                    channel_handshake_retry::default_strategy(max_block_times),
                                    |index| match RelayChannel::restore_from_state(
                                        chains.a.clone(),
                                        chains.b.clone(),
                                        channel.clone(),
                                        QueryHeight::Latest,
                                    ) {
                                        Ok((mut handshake_channel, state)) => {
                                            handshake_channel.step_state(state, index)
                                        }
                                        Err(_) => RetryResult::Retry(index),
                                    },
                                )
                                .map_err(|e| TaskError::Fatal(Box::new(RunError::retry(e)))),

                                IbcEventType::UpgradeErrorChannel => retry_with_index(
                                    channel_handshake_retry::default_strategy(max_block_times),
                                    |index| match RelayChannel::restore_from_state(
                                        chains.a.clone(),
                                        chains.b.clone(),
                                        channel.clone(),
                                        QueryHeight::Latest,
                                    ) {
                                        Ok((handshake_channel, _)) => {
                                            match handshake_channel
                                                .build_chan_upgrade_cancel_and_send()
                                            {
                                                Ok(_) => RetryResult::Ok(Next::Abort),
                                                Err(e) => {
                                                    warn!("Channel upgrade cancel failed: {e}");
                                                    RetryResult::Retry(index)
                                                }
                                            }
                                        }
                                        Err(_) => RetryResult::Retry(index),
                                    },
                                )
                                .map_err(|e| TaskError::Fatal(RunError::retry(e).into())),

                                _ => retry_with_index(
                                    channel_handshake_retry::default_strategy(max_block_times),
                                    |index| match RelayChannel::restore_from_event(
                                        chains.a.clone(),
                                        chains.b.clone(),
                                        event_with_height.event.clone(),
                                    ) {
                                        Ok(mut handshake_channel) => handshake_channel
                                            .step_event(&event_with_height.event, index),
                                        Err(_) => RetryResult::Retry(index),
                                    },
                                )
                                .map_err(|e| TaskError::Fatal(RunError::retry(e).into())),
                            }
                        } else {
                            Ok(Next::Continue)
                        }
                    }

                    WorkerCmd::NewBlock {
                        height: current_height,
                        new_block: _,
                    } if complete_handshake_on_new_block => {
                        debug!("starts processing block event at {:#?}", current_height);

                        complete_handshake_on_new_block = false;

                        retry_with_index(
                            channel_handshake_retry::default_strategy(max_block_times),
                            |index| match RelayChannel::restore_from_state(
                                chains.a.clone(),
                                chains.b.clone(),
                                channel.clone(),
                                QueryHeight::Latest,
                            ) {
                                Ok((mut handshake_channel, state)) => {
                                    handshake_channel.step_state(state, index)
                                }
                                Err(_) => RetryResult::Retry(index),
                            },
                        )
                        .map_err(|e| TaskError::Fatal(RunError::retry(e).into()))
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
