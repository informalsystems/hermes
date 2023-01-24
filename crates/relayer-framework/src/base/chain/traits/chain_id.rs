use crate::base::chain::traits::types::chain::HasChainTypes;

pub trait HasChainId: HasChainTypes {
    fn chain_id(&self) -> &Self::ChainId;
}
