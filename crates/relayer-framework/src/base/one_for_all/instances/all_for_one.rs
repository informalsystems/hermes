//! These functions bind the `one_for_all` trait to the `all_for_one`. Specifically,
//! this is where we 'prove' that the types that we want to implement the `all_for_one`
//! functionality implement the required trait bounds, i.e. `OfaRelayWrapper` or
//! `OfaChainWrapper`, etc.

use crate::base::all_for_one::traits::chain::AfoChainContext;
use crate::base::all_for_one::traits::error::AfoError;
use crate::base::all_for_one::traits::relay::AfoRelayContext;
use crate::base::one_for_all::traits::chain::{OfaChain, OfaChainWrapper, OfaIbcChain};
use crate::base::one_for_all::traits::components::chain::OfaIbcChainComponents;
use crate::base::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::base::one_for_all::traits::error::OfaError;
use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayWrapper};

/// Given a relay context `Relay` that implements the `OfaRelay` trait, returns a type
/// that implements the `AfoRelayContext`, meaning that this type exposes concrete APIs
/// that are used to construct custom relayer instances (i.e. relayer-cosmos).
pub fn afo_relay_context<Relay>(relay: OfaRelayWrapper<Relay>) -> impl AfoRelayContext
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    relay
}

/// Given a chain context `Chain` that implements the `OfaIbcChain` trait, returns a type
/// that implements the `AfoChainContext`, which is necessary for a relay context that
/// wants to relay between this IBC-enabled chain context and an IBC-enabled counterparty
/// chain context can do so.
pub fn afo_chain_context<Chain, Counterparty, Components>(
    chain: OfaChainWrapper<Chain>,
) -> impl AfoChainContext<OfaChainWrapper<Counterparty>>
where
    Chain: OfaChain<Components = Components>,
    Chain: OfaIbcChain<Counterparty>,
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
