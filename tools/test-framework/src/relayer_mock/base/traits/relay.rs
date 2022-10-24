use std::sync::Arc;

use ibc_relayer_framework::base::core::traits::sync::Async;

use crate::relayer_mock::base::traits::chain::MockChain;

pub trait MockRelay: Async {
    type SrcChain: MockChain;

    type DstChain: MockChain;

    fn src_chain(&self) -> &Arc<Self::SrcChain>;

    fn dst_chain(&self) -> &Arc<Self::DstChain>;

    fn src_to_dst_client(&self) -> &String;

    fn dst_to_src_client(&self) -> &String;
}
