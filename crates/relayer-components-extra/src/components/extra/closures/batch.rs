use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes;
use ibc_relayer_components::chain::traits::types::message::CanEstimateMessageSize;
use ibc_relayer_components::logger::traits::has_logger::HasLogger;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::components::ibc_message_sender::CanSendIbcMessages;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components::runtime::traits::time::HasTime;

use crate::batch::types::sink::BatchWorkerSink;
use crate::batch::worker::CanSpawnBatchMessageWorker;
use crate::runtime::traits::channel::{CanCloneSender, CanUseChannels, HasChannelTypes};
use crate::runtime::traits::channel_once::{CanUseChannelsOnce, HasChannelOnceTypes};
use crate::runtime::traits::spawn::HasSpawner;

pub trait CanUseBatchMessageWorkerSpawner: UseBatchMessageWorkerSpawner
where
    Self::SrcChain: HasRuntime,
    Self::DstChain: HasRuntime,
    <Self::SrcChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
    <Self::DstChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
}

pub trait UseBatchMessageWorkerSpawner:
    CanSpawnBatchMessageWorker<SourceTarget> + CanSpawnBatchMessageWorker<DestinationTarget>
where
    Self::SrcChain: HasRuntime,
    Self::DstChain: HasRuntime,
    <Self::SrcChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
    <Self::DstChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
}

impl<Relay, SrcChain, DstChain> UseBatchMessageWorkerSpawner for Relay
where
    Relay: Clone
        + HasLogger
        + HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanSendIbcMessages<BatchWorkerSink, SourceTarget>
        + CanSendIbcMessages<BatchWorkerSink, DestinationTarget>,
    SrcChain: HasRuntime + HasChainId + CanEstimateMessageSize + HasIbcChainTypes<DstChain>,
    DstChain: HasRuntime + HasChainId + CanEstimateMessageSize + HasIbcChainTypes<SrcChain>,
    SrcChain::Runtime: HasTime
        + HasMutex
        + CanSleep
        + HasSpawner
        + CanUseChannels
        + CanUseChannelsOnce
        + CanCloneSender,
    DstChain::Runtime: HasTime
        + HasMutex
        + CanSleep
        + HasSpawner
        + CanUseChannels
        + CanUseChannelsOnce
        + CanCloneSender,
    Relay::Error: Clone,
    Relay::Logger: HasBaseLogLevels,
{
}
