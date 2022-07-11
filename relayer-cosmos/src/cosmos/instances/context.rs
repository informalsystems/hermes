use ibc_relayer_framework::traits::chain_context::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::relay_context::RelayContext;

use crate::cosmos::handler::{CosmosChainHandler, CosmosRelayHandler};

pub fn relay_context<SrcChain, DstChain>(
    handler: &CosmosRelayHandler<SrcChain, DstChain>,
) -> &impl RelayContext
where
    SrcChain: Async,
    DstChain: Async,
{
    handler
}

pub fn chain_context<Chain>(handler: &CosmosChainHandler<Chain>) -> &impl ChainContext
where
    Chain: Async,
{
    handler
}

pub fn ibc_chain_context<Chain, Counterparty>(
    handler: &CosmosChainHandler<Chain>,
) -> &impl IbcChainContext<CosmosChainHandler<Counterparty>>
where
    Chain: Async,
    Counterparty: Async,
{
    handler
}
