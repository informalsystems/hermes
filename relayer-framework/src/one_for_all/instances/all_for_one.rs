use crate::all_for_one::traits::chain::{AfoChainContext, AfoCounterpartyContext};
use crate::all_for_one::traits::error::AfoError;
use crate::all_for_one::traits::relay::AfoRelayContext;
use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::error::OfaHasError;
use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::relay::OfaRelay;

pub fn afo_relay_context<Relay>(relay: OfaRelayContext<Relay>) -> impl AfoRelayContext
where
    Relay: OfaRelay,
{
    relay
}

pub fn afo_chain_context<Chain, Counterparty>(
    chain: OfaChainContext<Chain>,
) -> impl AfoChainContext<Counterparty>
where
    Chain: OfaChain,
    Counterparty: AfoCounterpartyContext<
        OfaChainContext<Chain>,
        Height = Chain::CounterpartyHeight,
        Sequence = Chain::CounterpartySequence,
        ConsensusState = Chain::CounterpartyConsensusState,
    >,
{
    chain
}

pub fn afo_error<Error>(error: OfaHasError<Error>) -> impl AfoError
where
    Error: OfaError,
{
    error
}
