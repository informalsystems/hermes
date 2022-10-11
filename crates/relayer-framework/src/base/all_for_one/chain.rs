use crate::base::chain::traits::context::{ChainContext, IbcChainContext};
use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::consensus_state::{
    HasConsensusState, HasConsensusStateQuerier,
};
use crate::base::chain::traits::queries::received_packet::HasReceivedPacketQuerier;
use crate::base::chain::traits::queries::status::HasChainStatusQuerier;

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
