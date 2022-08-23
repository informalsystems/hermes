use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::tokio::context::TokioRuntimeContext;

#[derive(Clone)]
pub struct CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub src_handle: OfaChainContext<CosmosChainContext<SrcChain>>,
    pub dst_handle: OfaChainContext<CosmosChainContext<DstChain>>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    pub runtime: OfaRuntimeContext<TokioRuntimeContext>,
}

impl<SrcChain, DstChain> CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new(
        runtime: TokioRuntimeContext,
        src_handle: CosmosChainContext<SrcChain>,
        dst_handle: CosmosChainContext<DstChain>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    ) -> Self {
        let runtime = OfaRuntimeContext::new(runtime);

        let context = Self {
            src_handle: OfaChainContext::new(src_handle),
            dst_handle: OfaChainContext::new(dst_handle),
            src_to_dst_client,
            dst_to_src_client,
            runtime,
        };

        context
    }
}
