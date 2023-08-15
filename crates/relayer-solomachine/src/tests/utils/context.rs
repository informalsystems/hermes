use std::sync::Arc;
use tokio::runtime::Runtime as TokioRuntime;

use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_cosmos::contexts::chain::CosmosChain;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::context::chain::MockSolomachineChainContext;
use crate::context::relay::SolomachineRelay;
use crate::types::chain::SolomachineChainWrapper;

pub fn solomachine_chain_context() -> SolomachineChainWrapper<MockSolomachineChainContext> {
    let commitment_prefix = "tmp-prefix".to_owned();
    let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(Arc::new(
        TokioRuntime::new().unwrap(),
    )));
    let chain = MockSolomachineChainContext::new(commitment_prefix, runtime);

    SolomachineChainWrapper::new(chain)
}

pub fn solomachine_to_cosmos_relay_context() -> OfaRelayWrapper<
    SolomachineRelay<
        SolomachineChainWrapper<MockSolomachineChainContext>,
        CosmosChain<BaseChainHandle>,
    >,
> {
    todo!()
}
