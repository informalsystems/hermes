use crate::all_for_one::traits::chain::AfoChainContext;
use crate::all_for_one::traits::error::AfoError;
use crate::all_for_one::traits::relay::AfoRelayContext;
use crate::one_for_all::traits::chain::{OfaChainContext, OfaIbcChain};
use crate::one_for_all::traits::components::chain::OfaIbcChainComponents;
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::relay::{OfaRelay, OfaRelayContext};

pub fn afo_relay_context<Relay>(relay: OfaRelayContext<Relay>) -> impl AfoRelayContext
where
    Relay: OfaRelay,
{
    relay
}

pub fn afo_chain_context<Chain, Counterparty, Components>(
    chain: OfaChainContext<Chain>,
) -> impl AfoChainContext<OfaChainContext<Counterparty>>
where
    Chain: OfaIbcChain<Counterparty, Components = Components>,
    Counterparty: OfaIbcChain<Chain>,
    Components: OfaIbcChainComponents<Chain, Counterparty>,
{
    chain
}

pub fn afo_error<Error>(error: OfaErrorContext<Error>) -> impl AfoError
where
    Error: OfaError,
{
    error
}
