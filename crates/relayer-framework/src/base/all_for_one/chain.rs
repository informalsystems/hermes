use crate::base::chain::traits::ibc_event::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::queries::consensus_state::{
    CanQueryConsensusState, HasConsensusState,
};
use crate::base::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::base::chain::traits::queries::status::CanQueryChainStatus;
use crate::base::chain::traits::types::{HasChainTypes, HasIbcChainTypes};

pub trait AfoBaseChain<Counterparty>:
    HasIbcChainTypes<Counterparty>
    + HasWriteAcknowledgementEvent<Counterparty>
    + HasConsensusState<Counterparty>
    + CanQueryConsensusState<Counterparty>
    + CanQueryReceivedPacket<Counterparty>
    + CanQueryChainStatus
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
        + HasWriteAcknowledgementEvent<Counterparty>
        + HasConsensusState<Counterparty>
        + CanQueryConsensusState<Counterparty>
        + CanQueryReceivedPacket<Counterparty>
        + CanQueryChainStatus,
{
}

impl<Chain, Counterparty> AfoCounterpartyChain<Chain> for Counterparty
where
    Chain: HasChainTypes,
    Counterparty: HasChainTypes + HasConsensusState<Chain>,
{
}
