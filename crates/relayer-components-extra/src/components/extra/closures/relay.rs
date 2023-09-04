use ibc_relayer_components::chain::traits::client::client_state::CanQueryClientState;
use ibc_relayer_components::chain::traits::components::chain_status_querier::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::logs::packet::CanLogChainPacket;
use ibc_relayer_components::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use ibc_relayer_components::chain::traits::message_builders::receive_packet::{
    CanBuildReceivePacketMessage, CanBuildReceivePacketPayload,
};
use ibc_relayer_components::chain::traits::message_builders::timeout_unordered_packet::{
    CanBuildTimeoutUnorderedPacketMessage, CanBuildTimeoutUnorderedPacketPayload,
};
use ibc_relayer_components::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::chain::traits::types::client_state::HasClientStateType;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use ibc_relayer_components::chain::traits::types::packet::HasIbcPacketFields;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::logger::traits::logger::BaseLogger;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::components::ibc_message_sender::{
    CanSendIbcMessages, MainSink,
};
use ibc_relayer_components::relay::traits::components::packet_filter::PacketFilter;
use ibc_relayer_components::relay::traits::components::packet_relayer::CanRelayPacket;
use ibc_relayer_components::relay::traits::components::packet_relayers::ack_packet::CanRelayAckPacket;
use ibc_relayer_components::relay::traits::components::packet_relayers::receive_packet::CanRelayReceivePacket;
use ibc_relayer_components::relay::traits::components::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use ibc_relayer_components::relay::traits::packet_lock::HasPacketLock;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::components::extra::relay::ExtraRelayComponents;
use crate::relay::components::packet_relayers::retry::SupportsPacketRetry;

pub trait UseExtraRelayComponents:
    CanRelayPacket + CanRelayAckPacket + CanRelayReceivePacket + CanRelayTimeoutUnorderedPacket
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
}

impl<Relay, BaseComponents> UseExtraRelayComponents for Relay
where
    Relay: HasRelayChains
        + HasLogger
        + HasPacketLock
        + HasComponents<Components = ExtraRelayComponents<BaseComponents>>
        + SupportsPacketRetry
        + CanSendIbcMessages<MainSink, SourceTarget>
        + CanSendIbcMessages<MainSink, DestinationTarget>,
    Relay::SrcChain: HasChainId
        + CanQueryChainStatus
        + HasLoggerType<Logger = Relay::Logger>
        + HasIbcPacketFields<Relay::DstChain>
        + CanLogChainPacket<Relay::DstChain>
        + CanQueryClientState<Relay::DstChain>
        + CanBuildReceivePacketPayload<Relay::DstChain>
        + CanBuildAckPacketMessage<Relay::DstChain>
        + CanBuildTimeoutUnorderedPacketMessage<Relay::DstChain>,
    Relay::DstChain: HasChainId
        + CanQueryChainStatus
        + CanQueryClientState<Relay::SrcChain>
        + CanQueryReceivedPacket<Relay::SrcChain>
        + HasWriteAcknowledgementEvent<Relay::SrcChain>
        + HasIbcPacketFields<Relay::SrcChain>
        + HasClientStateType<Relay::SrcChain>
        + CanBuildReceivePacketMessage<Relay::SrcChain>
        + CanBuildAckPacketPayload<Relay::SrcChain>
        + CanBuildTimeoutUnorderedPacketPayload<Relay::SrcChain>,
    Relay::Logger: HasBaseLogLevels,
    <Relay::SrcChain as HasLoggerType>::Logger: BaseLogger,
    BaseComponents: PacketFilter<Relay>,
{
}
