use crate::all_for_one::traits::chain::AfoChainContext;
use crate::all_for_one::traits::error::AfoError;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::ibc_message_sender::HasIbcMessageSender;
use crate::traits::messages::ack_packet::HasAckPacketMessageBuilder;
use crate::traits::messages::receive_packet::HasReceivePacketMessageBuilder;
use crate::traits::messages::update_client::HasUpdateClientMessageBuilder;
use crate::traits::target::{DestinationTarget, SourceTarget};

pub trait AfoRelayContext:
    RelayContext<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain, Error = Self::AfoError>
    + HasUpdateClientMessageBuilder<SourceTarget>
    + HasUpdateClientMessageBuilder<DestinationTarget>
    + HasIbcMessageSender<SourceTarget>
    + HasIbcMessageSender<DestinationTarget>
    + HasReceivePacketMessageBuilder
    + HasAckPacketMessageBuilder
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
        + HasAckPacketMessageBuilder,
{
    type AfoError = Error;

    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
