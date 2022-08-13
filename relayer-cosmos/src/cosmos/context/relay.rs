use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::traits::core::Async;
use tokio::runtime::Runtime;

use crate::cosmos::context::chain::CosmosChainContext;

#[derive(Clone)]
pub struct CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    pub src_handle: CosmosChainContext<SrcChain>,
    pub dst_handle: CosmosChainContext<DstChain>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    pub runtime: Arc<Runtime>,
}

impl<SrcChain, DstChain> CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new(
        src_handle: CosmosChainContext<SrcChain>,
        dst_handle: CosmosChainContext<DstChain>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    ) -> Self {
        let runtime = Arc::new(Runtime::new().unwrap());

        let context = Self {
            src_handle,
            dst_handle,
            src_to_dst_client,
            dst_to_src_client,
            runtime: runtime.clone(),
        };

        context
    }
}
