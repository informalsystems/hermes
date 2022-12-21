use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use tokio::sync::Mutex;

pub struct CosmosTxWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub nonce_mutex: Mutex<()>,
}

impl<Chain> CosmosTxWrapper<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: OfaRuntimeWrapper<TokioRuntimeContext>) -> Self {
        Self {
            chain,
            runtime,
            nonce_mutex: Mutex::new(()),
        }
    }
}
