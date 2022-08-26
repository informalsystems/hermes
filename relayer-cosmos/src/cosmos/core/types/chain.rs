use alloc::sync::Arc;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

#[derive(Clone)]
pub struct CosmosChainContext<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
}

impl<Chain> CosmosChainContext<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: CosmosRuntimeContext) -> Self {
        Self {
            chain,
            runtime: OfaRuntimeContext::new(runtime),
        }
    }
}
