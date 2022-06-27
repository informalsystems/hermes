use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::relay_types::CosmosRelayTypes;
use crate::traits::chain_types::IbcChainContext;
use crate::traits::core::ErrorContext;
use crate::traits::relay_types::RelayContext;

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

impl<Chain: ChainHandle> ErrorContext for CosmosChainHandler<Chain> {
    type Error = Error;
}

impl<Chain: ChainHandle> IbcChainContext<CosmosChainTypes> for CosmosChainHandler<Chain> {
    type IbcChainTypes = CosmosChainTypes;
}

impl<SrcChain, DstChain> ErrorContext for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type Error = Error;
}

impl<SrcChain, DstChain> RelayContext for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type RelayTypes = CosmosRelayTypes;

    type SrcChainContext = CosmosChainHandler<SrcChain>;

    type DstChainContext = CosmosChainHandler<DstChain>;

    fn source_context(&self) -> &Self::SrcChainContext {
        &self.src_handle
    }

    fn destination_context(&self) -> &Self::DstChainContext {
        &self.dst_handle
    }
}
