use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::types::batch::{BatchReceiver, BatchSender};

pub trait CosmosChainWithBatch: CosmosChain {
    fn batch_sender(&self) -> &BatchSender<Self>;

    fn batch_receiver(&self) -> &BatchReceiver<Self>;
}
