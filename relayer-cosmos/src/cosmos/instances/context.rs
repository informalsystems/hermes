use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;
use ibc_relayer_framework::traits::contexts::chain::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::contexts::relay::RelayContext;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;

pub fn relay_context<SrcChain, DstChain>(
    relay: CosmosRelayContext<SrcChain, DstChain>,
) -> impl RelayContext
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    OfaRelayContext::new(relay)
}

pub fn chain_context<Chain>(handler: CosmosChainContext<Chain>) -> impl ChainContext
where
    Chain: ChainHandle,
{
    OfaChainContext::new(handler)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    handler: CosmosChainContext<Chain>,
) -> impl IbcChainContext<OfaChainContext<CosmosChainContext<Counterparty>>>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    OfaChainContext::new(handler)
}
