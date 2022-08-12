use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::ibc_event::IbcEventContext;
use crate::traits::queries::consensus_state::{ConsensusStateContext, ConsensusStateQuerier};
use crate::traits::queries::received_packet::ReceivedPacketQuerier;
use crate::traits::queries::status::ChainStatusQuerierContext;

pub trait AfoChainContext<Counterparty>:
    IbcChainContext<Counterparty>
    + IbcEventContext<Counterparty>
    + ConsensusStateContext<Counterparty>
    + ConsensusStateQuerier<Counterparty>
    + ReceivedPacketQuerier<Counterparty>
    + ChainStatusQuerierContext
where
    Counterparty: AfoCounterpartyContext<Self>,
{
}

pub trait AfoCounterpartyContext<Chain>: ChainContext + ConsensusStateContext<Chain>
where
    Chain: ChainContext,
{
}

impl<Chain, Counterparty> AfoChainContext<Counterparty> for Chain
where
    Counterparty: ChainContext + ConsensusStateContext<Self>,
    Chain: IbcChainContext<Counterparty>
        + IbcEventContext<Counterparty>
        + ConsensusStateContext<Counterparty>
        + ConsensusStateQuerier<Counterparty>
        + ReceivedPacketQuerier<Counterparty>
        + ChainStatusQuerierContext,
{
}

impl<Chain, Counterparty> AfoCounterpartyContext<Chain> for Counterparty
where
    Chain: ChainContext,
    Counterparty: ChainContext + ConsensusStateContext<Chain>,
{
}
