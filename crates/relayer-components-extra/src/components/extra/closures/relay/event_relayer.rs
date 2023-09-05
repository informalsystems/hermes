use ibc_relayer_components::chain::traits::logs::packet::CanLogChainPacket;
use ibc_relayer_components::chain::traits::queries::channel::CanQueryCounterpartyChainIdFromChannel;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::CanBuildPacketFromWriteAckEvent;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::components::event_relayer::CanRelayEvent;
use ibc_relayer_components::relay::traits::components::packet_filter::PacketFilter;
use ibc_relayer_components::relay::traits::packet::HasRelayPacketFields;
use ibc_relayer_components::relay::traits::packet_lock::HasPacketLock;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::components::extra::closures::relay::ack_packet_relayer::UseExtraAckPacketRelayer;
use crate::components::extra::closures::relay::packet_relayer::UseExtraPacketRelayer;
use crate::components::extra::relay::ExtraRelayComponents;

pub trait CanUseExtraEventRelayer: UseExtraEventRelayer {}

pub trait UseExtraEventRelayer:
    CanRelayEvent<SourceTarget> + CanRelayEvent<DestinationTarget>
{
}

impl<Relay, BaseRelayComponents> UseExtraEventRelayer for Relay
where
    Relay: HasRelayChains
        + HasPacketLock
        + HasLogger
        + HasRelayPacketFields
        + UseExtraAckPacketRelayer
        + UseExtraPacketRelayer
        + HasComponents<Components = ExtraRelayComponents<BaseRelayComponents>>,
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
