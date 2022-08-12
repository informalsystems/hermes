use ibc_relayer_framework::traits::contexts::chain::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::contexts::relay::RelayContext;
use ibc_relayer_framework::traits::core::Async;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;

pub fn relay_context<SrcChain, DstChain>(
    handler: &CosmosRelayContext<SrcChain, DstChain>,
) -> &impl RelayContext
where
    SrcChain: Async,
    DstChain: Async,
{
    handler
}

pub fn chain_context<Chain>(handler: &CosmosChainContext<Chain>) -> &impl ChainContext
where
    Chain: Async,
{
    handler
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
