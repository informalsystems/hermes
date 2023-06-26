use alloc::string::String;
use std::sync::Arc;

use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;

pub struct MockRelayContext {
    pub src_chain: Arc<MockChainContext>,
    pub dst_chain: Arc<MockChainContext>,
    pub src_to_dst_client: String,
    pub dst_to_src_client: String,
    pub runtime: MockRuntimeContext,
}

impl MockRelayContext {
    pub fn new(
        src_chain: Arc<MockChainContext>,
        dst_chain: Arc<MockChainContext>,
        src_to_dst_client: String,
        dst_to_src_client: String,
        runtime: MockRuntimeContext,
    ) -> Self {
        Self {
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            runtime,
        }
    }

    pub fn src_chain(&self) -> &Arc<MockChainContext> {
        &self.src_chain
    }

    pub fn dst_chain(&self) -> &Arc<MockChainContext> {
        &self.dst_chain
    }

    pub fn src_to_dst_client(&self) -> &String {
        &self.src_to_dst_client
    }

    pub fn dst_to_src_client(&self) -> &String {
        &self.dst_to_src_client
    }
}
