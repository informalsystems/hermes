use ibc::{core::ics02_client::events::NewBlock, Height};

use crate::event::monitor::EventBatch;

/// A command for a [`WorkerHandle`](crate::worker::WorkerHandle).
#[derive(Debug, Clone)]
pub enum WorkerCmd {
    /// A batch of packet events need to be relayed
    IbcEvents { batch: EventBatch },

    /// A new block has been committed
    NewBlock { height: Height, new_block: NewBlock },

    /// Trigger a pending packets clear
    ClearPendingPackets,
}
