use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::client::consensus_state::CanFindConsensusStateHeight;
use crate::chain::traits::client::update::{
    CanBuildUpdateClientMessage, CanBuildUpdateClientPayload,
};
use crate::chain::traits::components::chain_status_querier::CanQueryChainStatus;
use crate::chain::traits::components::consensus_state_querier::CanQueryConsensusState;
use crate::chain::traits::components::message_sender::CanSendMessages;
use crate::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use crate::chain::traits::types::chain_id::HasChainId;
use crate::chain::traits::types::client_state::HasClientStateFields;
use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::traits::types::height::CanIncrementHeight;
use crate::chain::traits::types::ibc::HasCounterpartyMessageHeight;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::traits::types::packet::HasIbcPacketFields;
use crate::components::default::relay::DefaultRelayComponents;
use crate::core::traits::component::HasComponents;
use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;
use crate::logger::traits::has_logger::HasLogger;
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::traits::sleep::CanSleep;

pub trait CanUseDefaultAckPacketRelayer: UseDefaultAckPacketRelayer
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
}

pub trait UseDefaultAckPacketRelayer: CanRelayAckPacket
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
}

impl<Relay, SrcChain, DstChain, BaseRelayComponents> UseDefaultAckPacketRelayer for Relay
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + HasLogger
        + HasComponents<Components = DefaultRelayComponents<BaseRelayComponents>>,
    SrcChain: HasErrorType
        + HasChainId
        + CanSendMessages
        + HasConsensusStateType<DstChain>
        + HasCounterpartyMessageHeight<DstChain>
        + HasIbcPacketFields<DstChain, OutgoingPacket = Relay::Packet>
        + CanQueryClientState<DstChain>
        + CanQueryConsensusState<DstChain>
        + CanFindConsensusStateHeight<DstChain>
        + CanBuildAckPacketMessage<DstChain>
        + CanBuildUpdateClientMessage<DstChain>,
    DstChain: HasErrorType
        + HasRuntime
        + HasChainId
        + CanIncrementHeight
        + CanQueryChainStatus
        + HasClientStateFields<SrcChain>
        + HasConsensusStateType<SrcChain>
        + HasIbcPacketFields<SrcChain, IncomingPacket = Relay::Packet>
        + CanBuildAckPacketPayload<SrcChain>
        + CanBuildUpdateClientPayload<SrcChain>,
    SrcChain::Height: Clone,
    DstChain::Height: Clone,
    DstChain::Runtime: CanSleep,
    Relay::Logger: HasBaseLogLevels,
    BaseRelayComponents: Async,
{
}
