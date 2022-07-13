use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::traits::target::{ChainTarget, DestinationTarget, SourceTarget};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;

pub trait CosmosChainTarget<SrcChain, DstChain>:
    ChainTarget<
    CosmosRelayContext<SrcChain, DstChain>,
    TargetChain = CosmosChainContext<Self::TargetHandle>,
    CounterpartyChain = CosmosChainContext<Self::CounterpartyHandle>,
>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type TargetHandle: ChainHandle;

    type CounterpartyHandle: ChainHandle;

    fn target_handle(context: &CosmosRelayContext<SrcChain, DstChain>) -> &Self::TargetHandle;

    fn counterparty_handle(
        context: &CosmosRelayContext<SrcChain, DstChain>,
    ) -> &Self::CounterpartyHandle;

    fn target_foreign_client(
        context: &CosmosRelayContext<SrcChain, DstChain>,
    ) -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle>;
}

impl<SrcChain, DstChain> CosmosChainTarget<SrcChain, DstChain> for DestinationTarget
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type TargetHandle = DstChain;

    type CounterpartyHandle = SrcChain;

    fn target_handle(context: &CosmosRelayContext<SrcChain, DstChain>) -> &Self::TargetHandle {
        &context.dst_handle.handle
    }

    fn counterparty_handle(
        context: &CosmosRelayContext<SrcChain, DstChain>,
    ) -> &Self::CounterpartyHandle {
        &context.src_handle.handle
    }

    fn target_foreign_client(
        context: &CosmosRelayContext<SrcChain, DstChain>,
    ) -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle> {
        &context.src_to_dst_client
    }
}

impl<SrcChain, DstChain> CosmosChainTarget<SrcChain, DstChain> for SourceTarget
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type TargetHandle = SrcChain;

    type CounterpartyHandle = DstChain;

    fn target_handle(context: &CosmosRelayContext<SrcChain, DstChain>) -> &Self::TargetHandle {
        &context.src_handle.handle
    }

    fn counterparty_handle(
        context: &CosmosRelayContext<SrcChain, DstChain>,
    ) -> &Self::CounterpartyHandle {
        &context.dst_handle.handle
    }

    fn target_foreign_client(
        context: &CosmosRelayContext<SrcChain, DstChain>,
    ) -> &ForeignClient<Self::TargetHandle, Self::CounterpartyHandle> {
        &context.dst_to_src_client
    }
}
