use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::client::consensus_state::CanFindConsensusStateHeight;
use crate::chain::traits::client::update::{
    CanBuildUpdateClientMessage, CanBuildUpdateClientPayload,
};
use crate::chain::traits::components::chain_status_querier::CanQueryChainStatus;
use crate::chain::traits::components::consensus_state_querier::CanQueryConsensusState;
use crate::chain::traits::components::message_sender::CanSendMessages;
use crate::chain::traits::components::packet_fields_reader::CanReadPacketFields;
use crate::chain::traits::logs::packet::CanLogChainPacket;
use crate::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use crate::chain::traits::message_builders::receive_packet::{
    CanBuildReceivePacketMessage, CanBuildReceivePacketPayload,
};
use crate::chain::traits::message_builders::timeout_unordered_packet::{
    CanBuildTimeoutUnorderedPacketMessage, CanBuildTimeoutUnorderedPacketPayload,
};
use crate::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::chain::traits::types::chain_id::HasChainId;
use crate::chain::traits::types::client_state::HasClientStateFields;
use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::traits::types::height::CanIncrementHeight;
use crate::chain::traits::types::ibc::HasCounterpartyMessageHeight;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::components::default::relay::DefaultRelayComponents;
use crate::core::traits::component::HasComponents;
use crate::core::traits::error::HasErrorType;
use crate::logger::traits::has_logger::{HasLogger, HasLoggerType};
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::packet_filter::PacketFilter;
use crate::relay::traits::components::packet_relayer::CanRelayPacket;
use crate::relay::traits::packet_lock::HasPacketLock;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::traits::sleep::CanSleep;

pub trait CanUseDefaultPacketRelayer: UseDefaultPacketRelayer {}

pub trait UseDefaultPacketRelayer: CanRelayPacket {}

impl<Relay, SrcChain, DstChain, BaseRelayComponents> UseDefaultPacketRelayer for Relay
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + HasLogger
        + HasPacketLock
        + HasComponents<Components = DefaultRelayComponents<BaseRelayComponents>>,
    SrcChain: HasErrorType
        + HasRuntime
        + HasChainId
        + CanSendMessages
        + CanIncrementHeight
        + CanQueryChainStatus
        + HasLoggerType<Logger = Relay::Logger>
        + HasClientStateFields<DstChain>
        + HasConsensusStateType<DstChain>
        + HasCounterpartyMessageHeight<DstChain>
        + CanReadPacketFields<DstChain, OutgoingPacket = Relay::Packet>
        + CanLogChainPacket<DstChain>
        + CanQueryClientState<DstChain>
        + CanQueryConsensusState<DstChain>
        + CanFindConsensusStateHeight<DstChain>
        + CanBuildReceivePacketPayload<DstChain>
        + CanBuildUpdateClientPayload<DstChain>
        + CanBuildAckPacketMessage<DstChain>
        + CanBuildUpdateClientMessage<DstChain>
        + CanBuildTimeoutUnorderedPacketMessage<DstChain>,
    DstChain: HasErrorType
        + HasRuntime
        + HasChainId
        + CanSendMessages
        + CanIncrementHeight
        + CanQueryChainStatus
        + HasClientStateFields<SrcChain>
        + HasConsensusStateType<SrcChain>
        + HasCounterpartyMessageHeight<SrcChain>
        + HasWriteAcknowledgementEvent<SrcChain>
        + CanReadPacketFields<SrcChain, IncomingPacket = Relay::Packet>
        + CanQueryClientState<SrcChain>
        + CanQueryReceivedPacket<SrcChain>
        + CanQueryConsensusState<SrcChain>
        + CanFindConsensusStateHeight<SrcChain>
        + CanBuildAckPacketPayload<SrcChain>
        + CanBuildUpdateClientPayload<SrcChain>
        + CanBuildTimeoutUnorderedPacketPayload<SrcChain>
        + CanBuildUpdateClientMessage<SrcChain>
        + CanBuildReceivePacketMessage<SrcChain>,
    SrcChain::Height: Clone,
    DstChain::Height: Clone,
    SrcChain::Runtime: CanSleep,
    DstChain::Runtime: CanSleep,
    Relay::Logger: HasBaseLogLevels,
    BaseRelayComponents: PacketFilter<Relay>,
{
}
