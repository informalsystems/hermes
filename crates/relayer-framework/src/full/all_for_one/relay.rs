use crate::base::all_for_one::relay::AfoBaseRelay;
use crate::base::relay::traits::context::RelayContext;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::full::all_for_one::chain::AfoFullChain;
use crate::full::batch::message_sender::HasIbcMessageSenderForBatchWorker;
use crate::full::filter::traits::filter::HasPacketFilter;

pub trait AfoFullRelay:
    RelayContext<SrcChain = Self::AfoSrcFullChain, DstChain = Self::AfoDstFullChain>
    + AfoBaseRelay<AfoSrcChain = Self::AfoSrcFullChain, AfoDstChain = Self::AfoDstFullChain>
    + HasPacketFilter
    + HasIbcMessageSenderForBatchWorker<SourceTarget>
    + HasIbcMessageSenderForBatchWorker<DestinationTarget>
{
    type AfoSrcFullChain: AfoFullChain<Self::AfoDstFullChain>;
    type AfoDstFullChain: AfoFullChain<Self::AfoSrcFullChain>;
}

impl<Relay, SrcChain, DstChain> AfoFullRelay for Relay
where
    Relay: RelayContext<SrcChain = SrcChain, DstChain = DstChain>
        + AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain>
        + HasPacketFilter
        + HasIbcMessageSenderForBatchWorker<SourceTarget>
        + HasIbcMessageSenderForBatchWorker<DestinationTarget>,
    SrcChain: AfoFullChain<DstChain>,
    DstChain: AfoFullChain<SrcChain>,
{
    type AfoSrcFullChain = SrcChain;
    type AfoDstFullChain = DstChain;
}
