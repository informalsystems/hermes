use crate::all_for_one::traits::chain::AfoChainContext;
use crate::all_for_one::traits::error::AfoError;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::ibc_message_sender::HasIbcMessageSender;
use crate::core::traits::messages::ack_packet::HasAckPacketMessageBuilder;
use crate::core::traits::messages::receive_packet::HasReceivePacketMessageBuilder;
use crate::core::traits::messages::timeout_packet::HasTimeoutUnorderedPacketMessageBuilder;
use crate::core::traits::messages::update_client::HasUpdateClientMessageBuilder;
use crate::core::traits::target::{DestinationTarget, SourceTarget};

/// The functionality that a relay context gains access to once that relay
/// context implements the [`OfaRelayContext`] trait.
pub trait AfoRelayContext:
    RelayContext<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain, Error = Self::AfoError>
    + HasUpdateClientMessageBuilder<SourceTarget>
    + HasUpdateClientMessageBuilder<DestinationTarget>
    + HasIbcMessageSender<SourceTarget>
    + HasIbcMessageSender<DestinationTarget>
    + HasReceivePacketMessageBuilder
    + HasAckPacketMessageBuilder
    + HasTimeoutUnorderedPacketMessageBuilder
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
        + HasTimeoutUnorderedPacketMessageBuilder,
{
    type AfoError = Error;

    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
