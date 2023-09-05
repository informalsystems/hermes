use crate::chain::traits::logs::packet::CanLogChainPacket;
use crate::chain::traits::queries::channel::CanQueryCounterpartyChainIdFromChannel;
use crate::chain::traits::types::chain_id::HasChainId;
use crate::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use crate::chain::traits::types::ibc_events::write_ack::CanBuildPacketFromWriteAckEvent;
use crate::components::default::closures::relay::ack_packet_relayer::UseDefaultAckPacketRelayer;
use crate::components::default::closures::relay::packet_relayer::UseDefaultPacketRelayer;
use crate::components::default::relay::DefaultRelayComponents;
use crate::core::traits::component::HasComponents;
use crate::logger::traits::has_logger::{HasLogger, HasLoggerType};
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::event_relayer::CanRelayEvent;
use crate::relay::traits::components::packet_filter::PacketFilter;
use crate::relay::traits::packet::HasRelayPacketFields;
use crate::relay::traits::packet_lock::HasPacketLock;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};

pub trait CanUseDefaultEventRelayer: UseDefaultEventRelayer {}

pub trait UseDefaultEventRelayer:
    CanRelayEvent<SourceTarget> + CanRelayEvent<DestinationTarget>
{
}

impl<Relay, BaseRelayComponents> UseDefaultEventRelayer for Relay
where
    Relay: HasRelayChains
        + HasPacketLock
        + HasLogger
        + HasRelayPacketFields
        + UseDefaultAckPacketRelayer
        + UseDefaultPacketRelayer
        + HasComponents<Components = DefaultRelayComponents<BaseRelayComponents>>,
    Relay::SrcChain: HasChainId
        + HasLoggerType<Logger = Relay::Logger>
        + CanLogChainPacket<Relay::DstChain>
        + HasSendPacketEvent<Relay::DstChain>
        + CanQueryCounterpartyChainIdFromChannel<Relay::DstChain>,
    Relay::DstChain: HasChainId
        + CanQueryCounterpartyChainIdFromChannel<Relay::SrcChain>
        + CanBuildPacketFromWriteAckEvent<Relay::SrcChain>,
    Relay::Logger: HasBaseLogLevels,
    BaseRelayComponents: PacketFilter<Relay>,
{
}
