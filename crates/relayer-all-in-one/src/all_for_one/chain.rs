use crate::all_for_one::runtime::HasAfoBaseRuntime;
use crate::base::chain::traits::queries::consensus_state::CanQueryConsensusState;
use crate::base::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::base::chain::traits::queries::status::CanQueryChainStatus;
use crate::base::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::base::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::types::packet::HasIbcPacketTypes;

pub trait AfoBaseChain<Counterparty>:
    Clone
    + HasAfoBaseRuntime
    + HasIbcPacketTypes<Counterparty>
    + HasWriteAcknowledgementEvent<Counterparty>
    + HasConsensusStateType<Counterparty>
    + CanQueryConsensusState<Counterparty>
    + CanQueryReceivedPacket<Counterparty>
    + CanQueryChainStatus
where
    Counterparty: AfoCounterpartyChain<Self>,
{
}

pub trait AfoCounterpartyChain<Chain>:
    HasConsensusStateType<Chain>
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
    Chain: Clone
        + HasAfoBaseRuntime
        + HasIbcPacketTypes<Counterparty>
        + HasWriteAcknowledgementEvent<Counterparty>
        + HasConsensusStateType<Counterparty>
        + CanQueryConsensusState<Counterparty>
        + CanQueryReceivedPacket<Counterparty>
        + CanQueryChainStatus,
{
}

impl<Chain, Counterparty> AfoCounterpartyChain<Chain> for Counterparty
where
    Chain: HasIbcPacketTypes<Counterparty>,
    Counterparty: HasConsensusStateType<Chain>
        + HasIbcPacketTypes<
            Chain,
            IncomingPacket = Chain::OutgoingPacket,
            OutgoingPacket = Chain::IncomingPacket,
        >,
{
}
