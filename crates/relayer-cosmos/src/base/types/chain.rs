use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
}

impl<Chain> CosmosChainWrapper<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: OfaRuntimeWrapper<TokioRuntimeContext>) -> Self {
        Self { chain, runtime }
    }
}
