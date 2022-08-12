use crate::all_for_one::traits::chain::AfoChainContext;
use crate::all_for_one::traits::error::AfoError;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::ibc_message_sender::HasIbcMessageSender;
use crate::traits::messages::ack_packet::CanBuildAckPacketMessage;
use crate::traits::messages::receive_packet::CanBuildReceivePacketMessage;
use crate::traits::messages::update_client::CanUpdateClient;
use crate::traits::target::{DestinationTarget, SourceTarget};

pub trait AfoRelayContext:
    RelayContext<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain, Error = Self::AfoError>
    + CanUpdateClient<SourceTarget>
    + CanUpdateClient<DestinationTarget>
    + HasIbcMessageSender<SourceTarget>
    + HasIbcMessageSender<DestinationTarget>
    + CanBuildReceivePacketMessage
    + CanBuildAckPacketMessage
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
        + CanUpdateClient<SourceTarget>
        + CanUpdateClient<DestinationTarget>
        + HasIbcMessageSender<SourceTarget>
        + HasIbcMessageSender<DestinationTarget>
        + CanBuildReceivePacketMessage
        + CanBuildAckPacketMessage,
{
    type AfoError = Error;

    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
