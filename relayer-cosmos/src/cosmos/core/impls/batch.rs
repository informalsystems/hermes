use ibc_relayer_framework::one_for_all::traits::batch::OfaChainWithBatch;

use crate::cosmos::core::traits::batch::CosmosChainWithBatch;
use crate::cosmos::core::types::batch::CosmosBatchChannel;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

impl<Chain> OfaChainWithBatch for CosmosChainContext<Chain>
where
    Chain: CosmosChainWithBatch,
{
    type BatchContext = CosmosRuntimeContext;

    fn batch_channel(&self) -> &CosmosBatchChannel {
        self.chain.batch_channel()
    }
}
