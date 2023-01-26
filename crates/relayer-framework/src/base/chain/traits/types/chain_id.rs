use crate::base::core::traits::sync::Async;

pub trait HasChainIdType: Async {
    type ChainId: Eq + Async;
}

pub trait HasChainId: HasChainIdType {
    fn chain_id(&self) -> &Self::ChainId;
}
