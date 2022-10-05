use alloc::sync::Arc;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::core::traits::core::Async;

use crate::cosmos::core::traits::chain::CosmosChain;

pub trait CosmosRelay: Async {
    type Components;

    type SrcChain: CosmosChain<Components = Self::Components>;

    type DstChain: CosmosChain<Components = Self::Components>;

    fn src_chain(&self) -> &Arc<Self::SrcChain>;

    fn dst_chain(&self) -> &Arc<Self::DstChain>;

    fn src_to_dst_client(
        &self,
    ) -> &ForeignClient<
        <Self::DstChain as CosmosChain>::ChainHandle,
        <Self::SrcChain as CosmosChain>::ChainHandle,
    >;

    fn dst_to_src_client(
        &self,
    ) -> &ForeignClient<
        <Self::SrcChain as CosmosChain>::ChainHandle,
        <Self::DstChain as CosmosChain>::ChainHandle,
    >;
}
