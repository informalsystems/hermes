use ibc_relayer_components::chain::traits::queries::consensus_state::CanQueryConsensusState;
use ibc_relayer_components::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use ibc_relayer_components::chain::traits::queries::status::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes;

use crate::all_for_one::runtime::HasAfoBaseRuntime;

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
