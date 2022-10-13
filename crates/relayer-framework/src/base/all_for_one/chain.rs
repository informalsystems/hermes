use crate::base::chain::traits::context::{HasChainTypes, HasIbcChainTypes};
use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::consensus_state::{
    HasConsensusState, HasConsensusStateQuerier,
};
use crate::base::chain::traits::queries::received_packet::HasReceivedPacketQuerier;
use crate::base::chain::traits::queries::status::HasChainStatusQuerier;

pub trait AfoBaseChain<Counterparty>:
    HasIbcChainTypes<Counterparty>
    + HasIbcEvents<Counterparty>
    + HasConsensusState<Counterparty>
    + HasConsensusStateQuerier<Counterparty>
    + HasReceivedPacketQuerier<Counterparty>
    + HasChainStatusQuerier
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

pub trait AfoCounterpartyChain<Chain>: HasChainTypes + HasConsensusState<Chain>
where
    Chain: HasChainTypes,
{
}

impl<Chain, Counterparty> AfoBaseChain<Counterparty> for Chain
where
    Counterparty: HasChainTypes + HasConsensusState<Self>,
    Chain: HasIbcChainTypes<Counterparty>
        + HasIbcEvents<Counterparty>
        + HasConsensusState<Counterparty>
        + HasConsensusStateQuerier<Counterparty>
        + HasReceivedPacketQuerier<Counterparty>
        + HasChainStatusQuerier,
{
}

impl<Chain, Counterparty> AfoCounterpartyChain<Chain> for Counterparty
where
    Chain: HasChainTypes,
    Counterparty: HasChainTypes + HasConsensusState<Chain>,
{
}
