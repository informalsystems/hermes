use crate::base::all_for_one::relay::AfoBaseRelay;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::full::all_for_one::chain::AfoFullChain;
use crate::full::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use crate::full::relay::impls::packet_relayers::retry::SupportsPacketRetry;

pub trait AfoFullRelay:
    HasRelayTypes<SrcChain = Self::AfoSrcFullChain, DstChain = Self::AfoDstFullChain>
    + AfoBaseRelay<AfoSrcChain = Self::AfoSrcFullChain, AfoDstChain = Self::AfoDstFullChain>
    + CanSendIbcMessagesFromBatchWorker<SourceTarget>
    + CanSendIbcMessagesFromBatchWorker<DestinationTarget>
{
    type AfoSrcFullChain: AfoFullChain<
        Self::AfoDstFullChain,
        IncomingPacket = Self::AfoReversePacket,
        OutgoingPacket = Self::AfoPacket,
    >;
    type AfoDstFullChain: AfoFullChain<
        Self::AfoSrcFullChain,
        IncomingPacket = Self::AfoPacket,
        OutgoingPacket = Self::AfoReversePacket,
    >;
}

impl<Relay, SrcChain, DstChain> AfoFullRelay for Relay
where
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>
        + AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain>
        + CanSendIbcMessagesFromBatchWorker<SourceTarget>
        + CanSendIbcMessagesFromBatchWorker<DestinationTarget>
        + SupportsPacketRetry,
    SrcChain: AfoFullChain<
        DstChain,
        IncomingPacket = Relay::AfoReversePacket,
        OutgoingPacket = Relay::AfoPacket,
    >,
    DstChain: AfoFullChain<
        SrcChain,
        IncomingPacket = Relay::AfoPacket,
        OutgoingPacket = Relay::AfoReversePacket,
    >,
{
    type AfoSrcFullChain = SrcChain;
    type AfoDstFullChain = DstChain;
}
