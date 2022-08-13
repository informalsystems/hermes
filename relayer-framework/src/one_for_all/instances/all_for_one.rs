use crate::all_for_one::traits::chain::{AfoChainContext, AfoCounterpartyContext};
use crate::all_for_one::traits::error::AfoError;
use crate::all_for_one::traits::relay::AfoRelayContext;
use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::error::OfaErrorContext;
use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::components::chain::OfaChainWithComponents;
use crate::one_for_all::traits::components::relay::OfaRelayWithComponents;
use crate::one_for_all::traits::error::OfaError;

pub fn afo_relay_context<Relay>(relay: OfaRelayContext<Relay>) -> impl AfoRelayContext
where
    Relay: OfaRelayWithComponents,
{
    relay
}

pub fn afo_chain_context<Chain, Counterparty>(
    chain: OfaChainContext<Chain>,
) -> impl AfoChainContext<Counterparty>
where
    Chain: OfaChainWithComponents,
    Counterparty: AfoCounterpartyContext<
        OfaChainContext<Chain>,
        Height = Chain::CounterpartyHeight,
        Sequence = Chain::CounterpartySequence,
        ConsensusState = Chain::CounterpartyConsensusState,
    >,
{
    chain
}

pub fn afo_error<Error>(error: OfaErrorContext<Error>) -> impl AfoError
where
    Error: OfaError,
{
    error
}
