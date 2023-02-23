use ibc_relayer_all_in_one::all_for_one::relay::AfoBaseRelay;
use ibc_relayer_components::chain::types::aliases::{IncomingPacket, OutgoingPacket};
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components_extra::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use ibc_relayer_components_extra::relay::impls::packet_relayers::retry::SupportsPacketRetry;

use crate::all_for_one::chain::AfoFullChain;
use crate::all_for_one::runtime::HasAfoFullRuntime;

pub trait AfoFullRelay:
    HasAfoFullRuntime<AfoFullRuntime = Self::AfoBaseRuntime>
    + AfoBaseRelay<AfoSrcChain = Self::AfoSrcFullChain, AfoDstChain = Self::AfoDstFullChain>
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
    Relay: HasAfoFullRuntime<AfoFullRuntime = Self::AfoBaseRuntime>
        + AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain>
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
