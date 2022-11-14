use crate::base::all_for_one::relay::AfoBaseRelay;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::full::all_for_one::chain::AfoFullChain;
use crate::full::batch::message_sender::CanSendIbcMessagesFromBatchWorker;
use crate::full::filter::traits::filter::HasPacketFilter;
use crate::full::relay::impls::packet_relayers::retry::SupportsPacketRetry;

pub trait AfoFullRelay:
    HasRelayTypes<SrcChain = Self::AfoSrcFullChain, DstChain = Self::AfoDstFullChain>
    + AfoBaseRelay<AfoSrcChain = Self::AfoSrcFullChain, AfoDstChain = Self::AfoDstFullChain>
    + HasPacketFilter
    + CanSendIbcMessagesFromBatchWorker<SourceTarget>
    + CanSendIbcMessagesFromBatchWorker<DestinationTarget>
{
    type AfoSrcFullChain: AfoFullChain<Self::AfoDstFullChain>;
    type AfoDstFullChain: AfoFullChain<Self::AfoSrcFullChain>;
}

impl<Relay, SrcChain, DstChain> AfoFullRelay for Relay
where
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>
        + AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain>
        + HasPacketFilter
        + CanSendIbcMessagesFromBatchWorker<SourceTarget>
        + CanSendIbcMessagesFromBatchWorker<DestinationTarget>
        + SupportsPacketRetry,
    SrcChain: AfoFullChain<DstChain>,
    DstChain: AfoFullChain<SrcChain>,
{
    type AfoSrcFullChain = SrcChain;
    type AfoDstFullChain = DstChain;
}
