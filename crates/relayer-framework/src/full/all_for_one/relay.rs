use crate::base::all_for_one::relay::AfoRelayContext;
use crate::base::relay::traits::context::RelayContext;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::full::all_for_one::chain::AfoFullChainContext;
use crate::full::batch::message_sender::HasIbcMessageSenderForBatchWorker;
use crate::full::filter::traits::filter::HasPacketFilter;

pub trait AfoFullRelayContext:
    RelayContext<SrcChain = Self::AfoSrcFullChain, DstChain = Self::AfoDstFullChain>
    + AfoRelayContext<AfoSrcChain = Self::AfoSrcFullChain, AfoDstChain = Self::AfoDstFullChain>
    + HasPacketFilter
    + HasIbcMessageSenderForBatchWorker<SourceTarget>
    + HasIbcMessageSenderForBatchWorker<DestinationTarget>
{
    type AfoSrcFullChain: AfoFullChainContext<Self::AfoDstFullChain>;
    type AfoDstFullChain: AfoFullChainContext<Self::AfoSrcFullChain>;
}

impl<Relay, SrcChain, DstChain> AfoFullRelayContext for Relay
where
    Relay: RelayContext<SrcChain = SrcChain, DstChain = DstChain>
        + AfoRelayContext<AfoSrcChain = SrcChain, AfoDstChain = DstChain>
        + HasPacketFilter
        + HasIbcMessageSenderForBatchWorker<SourceTarget>
        + HasIbcMessageSenderForBatchWorker<DestinationTarget>,
    SrcChain: AfoFullChainContext<DstChain>,
    DstChain: AfoFullChainContext<SrcChain>,
{
    type AfoSrcFullChain = SrcChain;
    type AfoDstFullChain = DstChain;
}
