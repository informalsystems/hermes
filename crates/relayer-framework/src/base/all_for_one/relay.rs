use crate::base::all_for_one::chain::AfoBaseChain;
use crate::base::relay::traits::ibc_message_sender::CanSendIbcMessages;
use crate::base::relay::traits::messages::ack_packet::CanBuildAckPacketMessage;
use crate::base::relay::traits::messages::receive_packet::CanBuildReceivePacketMessage;
use crate::base::relay::traits::messages::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use crate::base::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
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
    + CanBuildReceivePacketMessage
    + CanBuildAckPacketMessage
    + CanBuildTimeoutUnorderedPacketMessage
    + CanRelayReceivePacket
    + CanRelayPacket
    + CanRelayAckPacket
    + CanRelayTimeoutUnorderedPacket
{
    type AfoSrcChain: AfoBaseChain<Self::AfoDstChain>;

    type AfoDstChain: AfoBaseChain<Self::AfoSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoBaseRelay for Relay
where
    SrcChain: AfoBaseChain<DstChain>,
    DstChain: AfoBaseChain<SrcChain>,
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>
        + CanBuildUpdateClientMessage<SourceTarget>
        + CanBuildUpdateClientMessage<DestinationTarget>
        + CanSendIbcMessages<SourceTarget>
        + CanSendIbcMessages<DestinationTarget>
        + CanBuildReceivePacketMessage
        + CanBuildAckPacketMessage
        + CanRelayReceivePacket
        + CanRelayPacket
        + CanRelayAckPacket
        + CanRelayTimeoutUnorderedPacket
        + CanBuildTimeoutUnorderedPacketMessage,
{
    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
