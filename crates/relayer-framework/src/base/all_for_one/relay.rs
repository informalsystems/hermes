use crate::base::all_for_one::chain::AfoBaseChain;
use crate::base::relay::impls::packet_relayers::general::retry::SupportsPacketRetry;
use crate::base::relay::traits::ibc_message_sender::HasIbcMessageSender;
use crate::base::relay::traits::ibc_message_sender::InjectMismatchIbcEventsCountError;
use crate::base::relay::traits::messages::ack_packet::HasAckPacketMessageBuilder;
use crate::base::relay::traits::messages::receive_packet::HasReceivePacketMessageBuilder;
use crate::base::relay::traits::messages::timeout_packet::HasTimeoutUnorderedPacketMessageBuilder;
use crate::base::relay::traits::messages::update_client::HasUpdateClientMessageBuilder;
use crate::base::relay::traits::packet_relayer::HasPacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::HasAckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::HasReceivePacketRelayer;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::HasTimeoutUnorderedPacketRelayer;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;

/// The functionality that a relay context gains access to once that relay
/// context implements the [`OfaRelayWrapper`] trait.
pub trait AfoBaseRelay:
    HasRelayTypes<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain>
    + HasUpdateClientMessageBuilder<SourceTarget>
    + HasUpdateClientMessageBuilder<DestinationTarget>
    + HasIbcMessageSender<SourceTarget>
    + HasIbcMessageSender<DestinationTarget>
    + HasReceivePacketMessageBuilder
    + HasAckPacketMessageBuilder
    + HasTimeoutUnorderedPacketMessageBuilder
    + HasReceivePacketRelayer
    + HasPacketRelayer
    + HasAckPacketRelayer
    + HasTimeoutUnorderedPacketRelayer
    + SupportsPacketRetry
    + InjectMismatchIbcEventsCountError
{
    type AfoSrcChain: AfoBaseChain<Self::AfoDstChain>;

    type AfoDstChain: AfoBaseChain<Self::AfoSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoBaseRelay for Relay
where
    SrcChain: AfoBaseChain<DstChain>,
    DstChain: AfoBaseChain<SrcChain>,
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>
        + HasUpdateClientMessageBuilder<SourceTarget>
        + HasUpdateClientMessageBuilder<DestinationTarget>
        + HasIbcMessageSender<SourceTarget>
        + HasIbcMessageSender<DestinationTarget>
        + HasReceivePacketMessageBuilder
        + HasAckPacketMessageBuilder
        + HasReceivePacketRelayer
        + HasPacketRelayer
        + HasAckPacketRelayer
        + HasTimeoutUnorderedPacketRelayer
        + HasTimeoutUnorderedPacketMessageBuilder
        + SupportsPacketRetry
        + InjectMismatchIbcEventsCountError,
{
    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
