use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;

use crate::cosmos::traits::chain::CosmosChain;

pub trait CosmosRelay {
    type SrcChain: CosmosChain;
    type DstChain: CosmosChain;

    fn src_chain_context() -> OfaChainContext<Self::SrcChain>;

    fn dst_chain_context() -> OfaChainContext<Self::DstChain>;

    fn src_to_dst_client() -> ForeignClient<
        <Self::DstChain as CosmosChain>::ChainHandle,
        <Self::SrcChain as CosmosChain>::ChainHandle,
    >;

    fn dst_to_src_client() -> ForeignClient<
        <Self::SrcChain as CosmosChain>::ChainHandle,
        <Self::DstChain as CosmosChain>::ChainHandle,
    >;
}
