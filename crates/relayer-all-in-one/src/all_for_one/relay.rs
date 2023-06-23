use ibc_relayer_components::chain::types::aliases::{IncomingPacket, OutgoingPacket};
use ibc_relayer_components::logger::traits::level::HasLoggerWithBaseLevels;
use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_components::relay::traits::event_relayer::CanRelayEvent;
use ibc_relayer_components::relay::traits::ibc_message_sender::CanSendIbcMessages;
use ibc_relayer_components::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use ibc_relayer_components::relay::traits::packet_filter::CanFilterPackets;
use ibc_relayer_components::relay::traits::packet_relayer::CanRelayPacket;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::relay::traits::types::HasRelayTypes;

use crate::all_for_one::chain::AfoChain;
use crate::all_for_one::runtime::HasAfoRuntime;

/// The functionality that a relay context gains access to once that relay
/// context implements the `OfaRelayWrapper` trait.
pub trait AfoRelay:
    Clone
    + HasAfoRuntime
    + HasLoggerWithBaseLevels
    + HasRelayTypes<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain>
    + CanBuildUpdateClientMessage<SourceTarget>
    + CanBuildUpdateClientMessage<DestinationTarget>
    + CanSendIbcMessages<SourceTarget>
    + CanSendIbcMessages<DestinationTarget>
    + CanRelayEvent<SourceTarget>
    + CanRelayEvent<DestinationTarget>
    + CanAutoRelay
    + CanFilterPackets
    + CanRelayReceivePacket
    + CanRelayPacket
    + CanRelayAckPacket
    + CanRelayTimeoutUnorderedPacket
{
    type AfoSrcChain: AfoChain<Self::AfoDstChain>;

    type AfoDstChain: AfoChain<
        Self::AfoSrcChain,
        IncomingPacket = OutgoingPacket<Self::AfoSrcChain, Self::AfoDstChain>,
        OutgoingPacket = IncomingPacket<Self::AfoSrcChain, Self::AfoDstChain>,
    >;
}

impl<Relay, SrcChain, DstChain, Packet, ReversePacket> AfoRelay for Relay
where
    SrcChain: AfoChain<DstChain, IncomingPacket = ReversePacket, OutgoingPacket = Packet>,
    DstChain: AfoChain<SrcChain, IncomingPacket = Packet, OutgoingPacket = ReversePacket>,
    Relay: Clone
        + HasAfoRuntime
        + HasLoggerWithBaseLevels
        + HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>
        + CanBuildUpdateClientMessage<SourceTarget>
        + CanBuildUpdateClientMessage<DestinationTarget>
        + CanSendIbcMessages<SourceTarget>
        + CanSendIbcMessages<DestinationTarget>
        + CanRelayEvent<SourceTarget>
        + CanRelayEvent<DestinationTarget>
        + CanAutoRelay
        + CanFilterPackets
        + CanRelayReceivePacket
        + CanRelayPacket
        + CanRelayAckPacket
        + CanRelayTimeoutUnorderedPacket,
{
    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
