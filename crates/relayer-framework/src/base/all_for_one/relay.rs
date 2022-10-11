use crate::base::all_for_one::chain::AfoChainContext;
use crate::base::all_for_one::error::AfoError;
use crate::base::relay::traits::context::RelayContext;
use crate::base::relay::traits::ibc_message_sender::HasIbcMessageSender;
use crate::base::relay::traits::messages::ack_packet::HasAckPacketMessageBuilder;
use crate::base::relay::traits::messages::receive_packet::HasReceivePacketMessageBuilder;
use crate::base::relay::traits::messages::timeout_packet::HasTimeoutUnorderedPacketMessageBuilder;
use crate::base::relay::traits::messages::update_client::HasUpdateClientMessageBuilder;
use crate::base::relay::traits::packet_relayer::HasPacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::HasAckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::HasReceivePacketRelayer;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::HasTimeoutUnorderedPacketRelayer;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};

/// The functionality that a relay context gains access to once that relay
/// context implements the [`OfaRelayWrapper`] trait.
pub trait AfoRelayContext:
    RelayContext<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain, Error = Self::AfoError>
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
{
    type AfoError: AfoError;

    type AfoSrcChain: AfoChainContext<Self::AfoDstChain>;

    type AfoDstChain: AfoChainContext<Self::AfoSrcChain>;
}

impl<Relay, SrcChain, DstChain, Error> AfoRelayContext for Relay
where
    Error: AfoError,
    SrcChain: AfoChainContext<DstChain>,
    DstChain: AfoChainContext<SrcChain>,
    Relay: RelayContext<SrcChain = SrcChain, DstChain = DstChain, Error = Error>
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
        + HasTimeoutUnorderedPacketMessageBuilder,
{
    type AfoError = Error;

    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
