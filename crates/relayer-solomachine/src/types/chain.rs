use crate::context::chain::MockSolomachineChainContext;

pub struct SolomachineChainWrapper<Chain> {
    pub chain: Chain,
}

impl SolomachineChainWrapper<Chain> {
    pub fn new(commitment_prefix: String, runtime: OfaRuntimeWrapper<TokioRuntimeContext>) -> Self {
        let chain = MockSolomachineChainContext::new(commitment_prefix, runtime);
        SolomachineChainWrapper { chain }
    }
}
