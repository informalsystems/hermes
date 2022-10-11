use crate::base::chain::traits::context::{ChainContext, IbcChainContext};
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainWrapper, OfaIbcChain};
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayWrapper};
use crate::base::relay::traits::context::RelayContext;

pub fn relay_context<Relay: OfaBaseRelay>(relay: Relay) -> impl RelayContext {
    OfaRelayWrapper::new(relay)
}

pub fn chain_context<Chain: OfaBaseChain>(chain: Chain) -> impl ChainContext {
    OfaChainWrapper::new(chain)
}

pub fn ibc_chain_context<Chain, Counterparty>(
    chain: Chain,
) -> impl IbcChainContext<OfaChainWrapper<Counterparty>>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
{
    OfaChainWrapper::new(chain)
}
