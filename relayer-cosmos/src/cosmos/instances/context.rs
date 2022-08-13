use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::one_for_all::impls::chain::OfaChainContext;
use ibc_relayer_framework::traits::contexts::chain::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::contexts::relay::RelayContext;
use ibc_relayer_framework::traits::core::Async;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;
use crate::cosmos::context::runtime::CosmosRuntime;

pub fn relay_context<SrcChain, DstChain>(
    handler: &CosmosRelayContext<SrcChain, DstChain>,
) -> &impl RelayContext
where
    SrcChain: Async,
    DstChain: Async,
{
    handler
}

pub fn chain_context<Chain>(handler: CosmosChainContext<Chain>) -> impl ChainContext
where
    Chain: ChainHandle,
{
    OfaChainContext::new(handler, CosmosRuntime)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    handler: &CosmosChainContext<Chain>,
) -> &impl IbcChainContext<CosmosChainContext<Counterparty>>
where
    Chain: Async,
    Counterparty: Async,
{
    handler
}
