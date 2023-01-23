use crate::base::all_for_one::chain::AfoBaseChain;
use crate::base::relay::traits::auto_relayer::CanAutoRelay;
use crate::base::relay::traits::event_relayer::CanRelayEvent;
use crate::base::relay::traits::ibc_message_sender::CanSendIbcMessages;
use crate::base::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::base::relay::traits::packet_filter::CanFilterPackets;
use crate::base::relay::traits::packet_relayer::CanRelayPacket;
use crate::base::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::base::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;

/// The functionality that a relay context gains access to once that relay
/// context implements the `OfaRelayWrapper` trait.
pub trait AfoBaseRelay:
    HasRelayTypes<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain>
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
    type AfoSrcChain: AfoBaseChain<
        Self::AfoDstChain,
        IncomingPacket = Self::AfoReversePacket,
        OutgoingPacket = Self::AfoPacket,
    >;

    type AfoDstChain: AfoBaseChain<
        Self::AfoSrcChain,
        IncomingPacket = Self::AfoPacket,
        OutgoingPacket = Self::AfoReversePacket,
    >;

    type AfoPacket;

    type AfoReversePacket;
}

impl<Relay, SrcChain, DstChain, Packet, ReversePacket> AfoBaseRelay for Relay
where
    SrcChain: AfoBaseChain<DstChain, IncomingPacket = ReversePacket, OutgoingPacket = Packet>,
    DstChain: AfoBaseChain<SrcChain, IncomingPacket = Packet, OutgoingPacket = ReversePacket>,
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>
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

    type AfoPacket = Packet;

    type AfoReversePacket = ReversePacket;
}
