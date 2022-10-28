use std::sync::Arc;

use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;

use crate::relayer_mock::base::types::runtime::MockRuntimeContext;

use super::chain::MockChainContext;

pub struct MockRelayContext {
    pub src_chain: Arc<OfaChainWrapper<MockChainContext>>,
    pub dst_chain: Arc<OfaChainWrapper<MockChainContext>>,
    pub src_to_dst_client: String,
    pub dst_to_src_client: String,
    pub runtime: OfaRuntimeContext<MockRuntimeContext>,
}

impl MockRelayContext {
    pub fn new(
        src_chain: Arc<OfaChainWrapper<MockChainContext>>,
        dst_chain: Arc<OfaChainWrapper<MockChainContext>>,
        src_to_dst_client: String,
        dst_to_src_client: String,
        runtime: MockRuntimeContext,
    ) -> Self {
        let runtime = OfaRuntimeContext::new(runtime);
        Self {
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            runtime,
        }
    }

    pub fn src_chain(&self) -> &Arc<OfaChainWrapper<MockChainContext>> {
        &self.src_chain
    }

    pub fn dst_chain(&self) -> &Arc<OfaChainWrapper<MockChainContext>> {
        &self.dst_chain
    }

    pub fn src_to_dst_client(&self) -> &String {
        &self.src_to_dst_client
    }

    pub fn dst_to_src_client(&self) -> &String {
        &self.dst_to_src_client
    }
}
