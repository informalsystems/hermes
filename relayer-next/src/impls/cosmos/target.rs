use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::impls::cosmos::handler::CosmosRelayHandler;
use crate::impls::cosmos::relay_types::CosmosRelayTypes;
use crate::traits::target::{ChainTarget, DestinationTarget, SourceTarget};

pub trait CosmosChainTarget<Target>
where
    Target: ChainTarget<CosmosRelayTypes>,
{
    type TargetHandle: ChainHandle;

    type CounterpartyHandle: ChainHandle;

    fn target_handle(&self) -> &Self::TargetHandle;

    fn counterparty_handle(&self) -> &Self::CounterpartyHandle;

    fn target_foreign_client(&self)
        -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle>;
}

impl<SrcHandle, DstHandle> CosmosChainTarget<DestinationTarget>
    for CosmosRelayHandler<SrcHandle, DstHandle>
where
    SrcHandle: ChainHandle,
    DstHandle: ChainHandle,
{
    type TargetHandle = DstHandle;

    type CounterpartyHandle = SrcHandle;

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

impl<SrcHandle, DstHandle> CosmosChainTarget<SourceTarget>
    for CosmosRelayHandler<SrcHandle, DstHandle>
where
    SrcHandle: ChainHandle,
    DstHandle: ChainHandle,
{
    type TargetHandle = SrcHandle;

    type CounterpartyHandle = DstHandle;

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
