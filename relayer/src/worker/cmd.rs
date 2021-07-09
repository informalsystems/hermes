use ibc::{ics02_client::events::NewBlock, Height};

use crate::event::monitor::EventBatch;

/// A command for a [`Worker`].
#[derive(Debug, Clone)]
pub enum WorkerCmd {
    /// A batch of packet events need to be relayed
    IbcEvents { batch: EventBatch },

    /// A batch of [`NewBlock`] events need to be relayed
    NewBlock { height: Height, new_block: NewBlock },

    /// Shutdown the worker
    Shutdown,
}
