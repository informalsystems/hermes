use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

#[derive(Clone)]
pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<TokioRuntimeContext>,
}

impl<Chain> CosmosChainWrapper<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: TokioRuntimeContext) -> Self {
        Self {
            chain,
            runtime: OfaRuntimeContext::new(runtime),
        }
    }
}
