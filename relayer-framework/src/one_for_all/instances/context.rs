use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext, OfaIbcChain};
use crate::one_for_all::traits::relay::{OfaRelay, OfaRelayContext};
use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::relay::RelayContext;

pub fn relay_context<Relay: OfaRelay>(relay: Relay) -> impl RelayContext {
    OfaRelayContext::new(relay)
}

pub fn chain_context<Chain: OfaChain>(chain: Chain) -> impl ChainContext {
    OfaChainContext::new(chain)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    chain: Chain,
) -> impl IbcChainContext<OfaChainContext<Counterparty>>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    OfaChainContext::new(chain)
}
