use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::message_sender::MessageSenderContext;
use crate::traits::queries::consensus_state::{ConsensusStateContext, ConsensusStateQuerier};
use crate::traits::queries::received_packet::ReceivedPacketQuerier;
use crate::traits::queries::status::ChainStatusQuerierContext;

pub trait AfoChainContext<Counterparty>:
    IbcChainContext<Counterparty>
    + IbcEventContext<Counterparty>
    + ConsensusStateContext<Counterparty>
    + ConsensusStateQuerier<Counterparty>
    + ReceivedPacketQuerier<Counterparty>
    + MessageSenderContext
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
        + MessageSenderContext
        + ChainStatusQuerierContext,
{
}

impl<Chain, Counterparty> AfoCounterpartyContext<Chain> for Counterparty
where
    Chain: ChainContext,
    Counterparty: ChainContext + ConsensusStateContext<Chain>,
{
}
