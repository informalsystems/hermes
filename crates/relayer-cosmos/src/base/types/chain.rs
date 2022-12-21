use alloc::sync::Arc;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::base::one_for_all::types::transaction::OfaTxWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::types::transaction::CosmosTxWrapper;

pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub tx_context: OfaTxWrapper<CosmosTxWrapper<Chain>>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
}

impl<Chain> CosmosChainWrapper<Chain> {
    pub fn new(chain: Arc<Chain>, runtime: OfaRuntimeWrapper<TokioRuntimeContext>) -> Self {
        let tx_context = OfaTxWrapper::new(CosmosTxWrapper::new(chain.clone(), runtime.clone()));

        Self {
            chain,
            runtime,
            tx_context,
        }
    }
}
