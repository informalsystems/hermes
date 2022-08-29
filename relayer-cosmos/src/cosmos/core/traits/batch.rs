use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::types::batch::CosmosBatchChannel;

pub trait CosmosChainWithBatch: CosmosChain {
    fn batch_channel(&self) -> &CosmosBatchChannel;
}
