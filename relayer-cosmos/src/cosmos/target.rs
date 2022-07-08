use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::traits::target::{ChainTarget, DestinationTarget, SourceTarget};

use crate::cosmos::handler::CosmosRelayHandler;

pub trait CosmosChainTarget<SrcChain, DstChain, Target>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<CosmosRelayHandler<SrcChain, DstChain>>,
{
    type TargetHandle: ChainHandle;

    type CounterpartyHandle: ChainHandle;

    fn target_handle(&self) -> &Self::TargetHandle;

    fn counterparty_handle(&self) -> &Self::CounterpartyHandle;

    fn target_foreign_client(&self)
        -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle>;
}

impl<SrcChain, DstChain> CosmosChainTarget<SrcChain, DstChain, DestinationTarget>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type TargetHandle = DstChain;

    type CounterpartyHandle = SrcChain;

    fn target_handle(&self) -> &Self::TargetHandle {
        &self.dst_handle.handle
    }

    fn counterparty_handle(&self) -> &Self::CounterpartyHandle {
        &self.src_handle.handle
    }

    fn target_foreign_client(
        &self,
    ) -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle> {
        &self.src_to_dst_client
    }
}

impl<SrcChain, DstChain> CosmosChainTarget<SrcChain, DstChain, SourceTarget>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type TargetHandle = SrcChain;

    type CounterpartyHandle = DstChain;

    fn target_handle(&self) -> &Self::TargetHandle {
        &self.src_handle.handle
    }

    fn counterparty_handle(&self) -> &Self::CounterpartyHandle {
        &self.dst_handle.handle
    }

    fn target_foreign_client(
        &self,
    ) -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle> {
        &self.dst_to_src_client
    }
}
