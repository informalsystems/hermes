use crate::base::all_for_one::relay::AfoBaseRelay;
use crate::base::chain::types::aliases::{IncomingPacket, OutgoingPacket};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::full::all_for_one::chain::AfoFullChain;
use crate::full::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use crate::full::relay::impls::packet_relayers::retry::SupportsPacketRetry;

pub trait AfoFullRelay:
    AfoBaseRelay<AfoSrcChain = Self::AfoSrcFullChain, AfoDstChain = Self::AfoDstFullChain>
    + CanSendIbcMessagesFromBatchWorker<SourceTarget>
    + CanSendIbcMessagesFromBatchWorker<DestinationTarget>
    + SupportsPacketRetry
{
    type AfoSrcFullChain: AfoFullChain<Self::AfoDstFullChain>;

    type AfoDstFullChain: AfoFullChain<
        Self::AfoSrcFullChain,
        IncomingPacket = OutgoingPacket<Self::AfoSrcChain, Self::AfoDstChain>,
        OutgoingPacket = IncomingPacket<Self::AfoSrcChain, Self::AfoDstChain>,
    >;
}

impl<Relay, SrcChain, DstChain> AfoFullRelay for Relay
where
    Relay: AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain>
        + CanSendIbcMessagesFromBatchWorker<SourceTarget>
        + CanSendIbcMessagesFromBatchWorker<DestinationTarget>
        + SupportsPacketRetry,
    SrcChain: AfoFullChain<DstChain>,
    DstChain: AfoFullChain<
        SrcChain,
        IncomingPacket = OutgoingPacket<SrcChain, DstChain>,
        OutgoingPacket = IncomingPacket<SrcChain, DstChain>,
    >,
{
    type AfoSrcFullChain = SrcChain;
    type AfoDstFullChain = DstChain;
}
