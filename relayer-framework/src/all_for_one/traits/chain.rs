use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::queries::consensus_state::{CanQueryConsensusState, HasConsensusState};
use crate::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::traits::queries::status::CanQueryChainStatus;

pub trait AfoChainContext<Counterparty>:
    IbcChainContext<Counterparty>
    + HasIbcEvents<Counterparty>
    + HasConsensusState<Counterparty>
    + CanQueryConsensusState<Counterparty>
    + CanQueryReceivedPacket<Counterparty>
    + CanQueryChainStatus
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
        + CanQueryConsensusState<Counterparty>
        + CanQueryReceivedPacket<Counterparty>
        + CanQueryChainStatus,
{
}

impl<Chain, Counterparty> AfoCounterpartyContext<Chain> for Counterparty
where
    Chain: ChainContext,
    Counterparty: ChainContext + HasConsensusState<Chain>,
{
}
