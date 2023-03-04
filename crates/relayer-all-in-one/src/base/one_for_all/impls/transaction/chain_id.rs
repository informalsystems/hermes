use ibc_relayer_components::chain::traits::types::chain_id::{HasChainId, HasChainIdType};

use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;

impl<TxContext> HasChainIdType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type ChainId = TxContext::ChainId;
}

impl<TxContext> HasChainId for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn chain_id(&self) -> &Self::ChainId {
        self.tx_context.chain_id()
    }
}
