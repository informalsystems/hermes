use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

#[derive(Clone)]
pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
}

impl<Chain> CosmosChainWrapper<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: CosmosRuntimeContext) -> Self {
        Self {
            chain,
            runtime: OfaRuntimeContext::new(runtime),
        }
    }
}
