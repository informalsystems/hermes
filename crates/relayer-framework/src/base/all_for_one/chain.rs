use crate::base::chain::traits::queries::consensus_state::{
    CanQueryConsensusState, HasConsensusState,
};
use crate::base::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::base::chain::traits::queries::status::CanQueryChainStatus;
use crate::base::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::types::packet::HasIbcPacketTypes;

pub trait AfoBaseChain<Counterparty>:
    HasIbcPacketTypes<Counterparty>
    + HasWriteAcknowledgementEvent<Counterparty>
    + HasConsensusState<Counterparty>
    + CanQueryConsensusState<Counterparty>
    + CanQueryReceivedPacket<Counterparty>
    + CanQueryChainStatus
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

pub trait AfoCounterpartyChain<Chain>:
    HasConsensusState<Chain>
    + HasIbcPacketTypes<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >
where
    Chain: HasIbcPacketTypes<Self>,
{
}

impl<Chain, Counterparty> AfoBaseChain<Counterparty> for Chain
where
    Counterparty: AfoCounterpartyChain<Self>,
    Chain: HasIbcPacketTypes<Counterparty>
        + HasWriteAcknowledgementEvent<Counterparty>
        + HasConsensusState<Counterparty>
        + CanQueryConsensusState<Counterparty>
        + CanQueryReceivedPacket<Counterparty>
        + CanQueryChainStatus,
{
}

impl<Chain, Counterparty> AfoCounterpartyChain<Chain> for Counterparty
where
    Chain: HasIbcPacketTypes<Counterparty>,
    Counterparty: HasConsensusState<Chain>
        + HasIbcPacketTypes<
            Chain,
            IncomingPacket = Chain::OutgoingPacket,
            OutgoingPacket = Chain::IncomingPacket,
        >,
{
}
