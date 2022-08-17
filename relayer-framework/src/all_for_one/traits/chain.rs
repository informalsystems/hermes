use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::queries::consensus_state::{HasConsensusState, HasConsensusStateQuerier};
use crate::traits::queries::received_packet::HasReceivedPacketQuerier;
use crate::traits::queries::status::HasChainStatusQuerier;

pub trait AfoChainContext<Counterparty>:
    IbcChainContext<Counterparty>
    + HasIbcEvents<Counterparty>
    + HasConsensusState<Counterparty>
    + HasConsensusStateQuerier<Counterparty>
    + HasReceivedPacketQuerier<Counterparty>
    + HasChainStatusQuerier
where
    Counterparty: AfoCounterpartyContext<Self>,
{
}

pub trait AfoCounterpartyContext<Chain>: ChainContext + HasConsensusState<Chain>
where
    Chain: ChainContext,
{
}

impl<Chain, Counterparty> AfoChainContext<Counterparty> for Chain
where
    Counterparty: ChainContext + HasConsensusState<Self>,
    Chain: IbcChainContext<Counterparty>
        + HasIbcEvents<Counterparty>
        + HasConsensusState<Counterparty>
        + HasConsensusStateQuerier<Counterparty>
        + HasReceivedPacketQuerier<Counterparty>
        + HasChainStatusQuerier,
{
}

impl<Chain, Counterparty> AfoCounterpartyContext<Chain> for Counterparty
where
    Chain: ChainContext,
    Counterparty: ChainContext + HasConsensusState<Chain>,
{
}
