use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::relay::RelayContext;

pub fn relay_context<Relay: OfaRelay>(relay: Relay) -> impl RelayContext {
    OfaRelayContext::new(relay)
}

pub fn chain_context<Chain: OfaChain>(chain: Chain) -> impl ChainContext {
    OfaChainContext::new(chain)
}

pub fn ibc_chain_context<Chain, Counterparty>(chain: Chain) -> impl IbcChainContext<Counterparty>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    OfaChainContext::new(chain)
}
