use core::fmt;

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

impl fmt::Display for WorkerCmd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WorkerCmd::IbcEvents { batch } => {
                write!(f, "IbcEvents batch from {}: ", batch.chain_id)?;
                for e in &batch.events {
                    write!(f, "{}; ", e)?;
                }
                write!(f, "batch Height: {}", batch.height)
            }
            WorkerCmd::NewBlock { height, new_block } => {
                write!(f, "NewBlock({}, {:?})", height, new_block)
            }
            WorkerCmd::ClearPendingPackets => write!(f, "CleaPendingPackets"),
        }
    }
}
