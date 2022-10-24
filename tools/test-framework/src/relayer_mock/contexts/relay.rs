use std::sync::Arc;

use crate::relayer_mock::base::traits::{chain::MockChain, relay::MockRelay};

pub struct MockRelayContext<SrcChain, DstChain>
where
    SrcChain: MockChain,
    DstChain: MockChain,
{
    pub src_chain: Arc<SrcChain>,
    pub dst_chain: Arc<DstChain>,
    pub src_to_dst_client: String,
    pub dst_to_src_client: String,
}

impl<SrcChain, DstChain> MockRelayContext<SrcChain, DstChain>
where
    SrcChain: MockChain,
    DstChain: MockChain,
{
    pub fn new(
        src_chain: Arc<SrcChain>,
        dst_chain: Arc<DstChain>,
        src_to_dst_client: String,
        dst_to_src_client: String,
    ) -> Self {
        Self {
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
        }
    }
}

impl<SrcChain, DstChain> MockRelay for MockRelayContext<SrcChain, DstChain>
where
    SrcChain: MockChain,
    DstChain: MockChain,
{
    type SrcChain = SrcChain;

    type DstChain = DstChain;

    fn src_chain(&self) -> &Arc<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &Arc<Self::DstChain> {
        &self.dst_chain
    }

    fn src_to_dst_client(&self) -> &String {
        &self.src_to_dst_client
    }

    fn dst_to_src_client(&self) -> &String {
        &self.dst_to_src_client
    }
}
