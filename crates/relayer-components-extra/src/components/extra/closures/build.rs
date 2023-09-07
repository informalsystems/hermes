use ibc_relayer_components::build::traits::birelay::HasBiRelayType;
use ibc_relayer_components::build::traits::cache::{HasChainCache, HasRelayCache};
use ibc_relayer_components::build::traits::components::birelay_builder::CanBuildBiRelay;
use ibc_relayer_components::build::traits::components::birelay_from_relay_builder::BiRelayFromRelayBuilder;
use ibc_relayer_components::build::traits::components::chain_builder::ChainBuilder;
use ibc_relayer_components::build::traits::target::chain::{ChainATarget, ChainBTarget};
use ibc_relayer_components::build::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::batch::traits::config::HasBatchConfig;
use crate::build::traits::cache::HasBatchSenderCache;
use crate::build::traits::components::relay_with_batch_builder::RelayWithBatchBuilder;
use crate::components::extra::build::ExtraBuildComponents;
use crate::components::extra::closures::batch::UseBatchMessageWorkerSpawner;
use crate::runtime::traits::channel::{CanCloneSender, CanCreateChannels};
use crate::runtime::traits::channel_once::CanUseChannelsOnce;

pub trait CanUseExtraBuilderComponents: UseExtraBuilderComponents {}

pub trait UseExtraBuilderComponents: CanBuildBiRelay {}

impl<Build, BiRelay, RelayAToB, RelayBToA, ChainA, ChainB, Error, BaseComponents>
    UseExtraBuilderComponents for Build
where
    Build: HasErrorType
        + HasRuntime
        + HasBatchConfig
        + HasBiRelayType<BiRelay = BiRelay>
        + HasRelayCache<RelayAToBTarget>
        + HasRelayCache<RelayBToATarget>
        + HasChainCache<ChainATarget>
        + HasChainCache<ChainBTarget>
        + HasBatchSenderCache<ChainATarget, Error>
        + HasBatchSenderCache<ChainBTarget, Error>
        + HasComponents<Components = ExtraBuildComponents<BaseComponents>>,
    BiRelay: HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
    RelayAToB: Clone
        + HasErrorType<Error = Error>
        + HasRelayChains<SrcChain = ChainA, DstChain = ChainB>
        + UseBatchMessageWorkerSpawner,
    RelayBToA: Clone
        + HasErrorType<Error = Error>
        + HasRelayChains<SrcChain = ChainB, DstChain = ChainA>
        + UseBatchMessageWorkerSpawner,
    ChainA: Clone + HasRuntime + HasChainId + HasIbcChainTypes<ChainB>,
    ChainB: Clone + HasRuntime + HasChainId + HasIbcChainTypes<ChainA>,
    Error: Async,
    ChainA::ChainId: Ord + Clone,
    ChainB::ChainId: Ord + Clone,
    ChainA::ClientId: Ord + Clone,
    ChainB::ClientId: Ord + Clone,
    ChainA::Runtime: CanCreateChannels + CanUseChannelsOnce + CanCloneSender,
    ChainB::Runtime: CanCreateChannels + CanUseChannelsOnce + CanCloneSender,
    Build::Runtime: HasMutex,
    BaseComponents: BiRelayFromRelayBuilder<Build>
        + RelayWithBatchBuilder<Build, RelayAToBTarget>
        + RelayWithBatchBuilder<Build, RelayBToATarget>
        + ChainBuilder<Build, ChainATarget>
        + ChainBuilder<Build, ChainBTarget>,
{
}
