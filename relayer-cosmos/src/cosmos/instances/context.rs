use ibc_relayer_framework::traits::chain_context::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::relay_context::RelayContext;

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
