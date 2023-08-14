use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use std::sync::Arc;
use tokio::runtime::Runtime as TokioRuntime;

use crate::context::chain::MockSolomachineChainContext;
use crate::types::chain::SolomachineChainWrapper;

pub fn solomachine_chain_context() -> SolomachineChainWrapper<MockSolomachineChainContext> {
    let commitment_prefix = "tmp-prefix".to_owned();
    let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(Arc::new(
        TokioRuntime::new().unwrap(),
    )));
    let chain = MockSolomachineChainContext::new(commitment_prefix, runtime);

    SolomachineChainWrapper::new(chain)
}
