use crate::base::one_for_all::traits::chain::{OfaChain, OfaChainWrapper, OfaIbcChain};
use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayWrapper};
use crate::base::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::base::traits::contexts::relay::RelayContext;

pub fn relay_context<Relay: OfaRelay>(relay: Relay) -> impl RelayContext {
    OfaRelayWrapper::new(relay)
}

pub fn chain_context<Chain: OfaChain>(chain: Chain) -> impl ChainContext {
    OfaChainWrapper::new(chain)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    chain: Chain,
) -> impl IbcChainContext<OfaChainWrapper<Counterparty>>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    OfaChainWrapper::new(chain)
}
