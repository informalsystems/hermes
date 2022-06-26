use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::impls::cosmos::relay_types::CosmosRelayTypes;
use crate::traits::chain_types::IbcChainContext;
use crate::traits::relay_types::RelayContext;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

pub struct CosmosChainHandler<Handle: ChainHandle> {
    pub handle: Handle,
}

pub struct CosmosRelayHandler<SrcHandle, DstHandle>
where
    SrcHandle: ChainHandle,
    DstHandle: ChainHandle,
{
    pub src_handle: CosmosChainHandler<SrcHandle>,
    pub dst_handle: CosmosChainHandler<DstHandle>,
    pub src_to_dst_client: ForeignClient<DstHandle, SrcHandle>,
    pub dst_to_src_client: ForeignClient<SrcHandle, DstHandle>,
}

impl<Chain: ChainHandle> IbcChainContext<CosmosChainTypes> for CosmosChainHandler<Chain> {
    type IbcChainTypes = CosmosChainTypes;
}

impl<SrcChain, DstChain> RelayContext for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type RelayTypes = CosmosRelayTypes;

    type SrcChain = CosmosChainHandler<SrcChain>;

    type DstChain = CosmosChainHandler<DstChain>;

    fn source_context(&self) -> &Self::SrcChain {
        &self.src_handle
    }

    fn destination_context(&self) -> &Self::DstChain {
        &self.dst_handle
    }
}
