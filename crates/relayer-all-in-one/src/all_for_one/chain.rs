use ibc_relayer_components::chain::traits::client::create::HasCreateClientOptions;
use ibc_relayer_components::chain::traits::queries::consensus_state::CanQueryConsensusState;
use ibc_relayer_components::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;
use ibc_relayer_components::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use ibc_relayer_components::chain::traits::queries::status::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::types::channel::{
    HasChannelHandshakePayloads, HasInitChannelOptionsType,
};
use ibc_relayer_components::chain::traits::types::connection::{
    HasConnectionHandshakePayloads, HasInitConnectionOptionsType,
};
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes;
use ibc_relayer_components::logger::traits::level::HasLoggerWithBaseLevels;
use ibc_relayer_components_extra::telemetry::traits::telemetry::HasTelemetry;

use crate::all_for_one::runtime::HasAfoRuntime;

pub trait AfoChain<Counterparty>:
    Clone
    + HasAfoRuntime
    + HasLoggerWithBaseLevels
    + HasTelemetry
    + CanQueryChainStatus
    + HasIbcPacketTypes<Counterparty>
    + HasWriteAcknowledgementEvent<Counterparty>
    + HasConsensusStateType<Counterparty>
    + CanQueryConsensusState<Counterparty>
    + CanQueryReceivedPacket<Counterparty>
    + CanQueryPacketCommitments<Counterparty>
    + HasCreateClientOptions<Counterparty>
    + HasInitConnectionOptionsType<Counterparty>
    + HasConnectionHandshakePayloads<Counterparty>
    + HasInitChannelOptionsType<Counterparty>
    + HasChannelHandshakePayloads<Counterparty>
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

impl<Chain, Counterparty> AfoChain<Counterparty> for Chain
where
    Counterparty: AfoCounterpartyChain<Self>,
    Chain: Clone
        + HasAfoRuntime
        + HasLoggerWithBaseLevels
        + HasTelemetry
        + CanQueryChainStatus
        + HasIbcPacketTypes<Counterparty>
        + HasWriteAcknowledgementEvent<Counterparty>
        + HasConsensusStateType<Counterparty>
        + CanQueryConsensusState<Counterparty>
        + CanQueryReceivedPacket<Counterparty>
        + CanQueryPacketCommitments<Counterparty>
        + HasCreateClientOptions<Counterparty>
        + HasInitConnectionOptionsType<Counterparty>
        + HasConnectionHandshakePayloads<Counterparty>
        + HasInitChannelOptionsType<Counterparty>
        + HasChannelHandshakePayloads<Counterparty>,
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
