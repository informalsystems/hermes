use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::relay::RelayFromChainsBuilder;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::chain::traits::types::chain_id::HasChainId;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::mutex::{HasMutex, HasRuntimeWithMutex};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::traits::config::HasBatchConfig;
use crate::full::batch::types::aliases::MessageBatchSender;
use crate::full::batch::worker::CanSpawnBatchMessageWorker;
use crate::full::builder::traits::cache::HasBatchSenderCache;
use crate::full::builder::traits::relay::RelayWithBatchBuilder;
use crate::full::runtime::traits::channel::CanCreateChannels;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;
use crate::std_prelude::*;

pub struct BuildBatchWorker<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<Build, InBuilder, Target, Relay, SrcChain, DstChain, SrcRuntime, DstRuntime>
    RelayFromChainsBuilder<Build, Target> for BuildBatchWorker<InBuilder>
where
    Build: HasBiRelayType
        + HasRuntimeWithMutex
        + HasBatchConfig
        + HasErrorType
        + HasBatchSenderCache<Target::SrcChainTarget, Relay::Error>
        + HasBatchSenderCache<Target::DstChainTarget, Relay::Error>,
    Target: RelayBuildTarget<Build, TargetRelay = Relay>,
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain>,
    Relay: CanSpawnBatchMessageWorker<SourceTarget>
        + CanSpawnBatchMessageWorker<DestinationTarget>
        + Clone,
    SrcChain: HasIbcChainTypes<DstChain>,
    DstChain: HasIbcChainTypes<SrcChain>,
    SrcChain: HasRuntime<Runtime = SrcRuntime> + HasChainId,
    DstChain: HasRuntime<Runtime = DstRuntime> + HasChainId,
    SrcChain::ChainId: Ord + Clone,
    DstChain::ChainId: Ord + Clone,
    SrcChain::ClientId: Ord + Clone,
    DstChain::ClientId: Ord + Clone,
    InBuilder: RelayWithBatchBuilder<Build, Target>,
    SrcRuntime: CanCreateChannels + HasChannelOnceTypes,
    DstRuntime: CanCreateChannels + HasChannelOnceTypes,
    MessageBatchSender<SrcChain, Relay::Error>: Clone,
    MessageBatchSender<DstChain, Relay::Error>: Clone,
{
    async fn build_relay_from_chains(
        build: &Build,
        _target: Target,
        src_client_id: &SrcChain::ClientId,
        dst_client_id: &DstChain::ClientId,
        src_chain: SrcChain,
        dst_chain: DstChain,
    ) -> Result<Target::TargetRelay, Build::Error> {
        let src_chain_id = src_chain.chain_id();
        let dst_chain_id = dst_chain.chain_id();

        let (src_sender, m_src_receiver) = {
            let mutex = build.batch_sender_cache(Target::SrcChainTarget::default());

            let mut sender_cache_a = Build::Runtime::acquire_mutex(mutex).await;
            let cache_key = (
                src_chain_id.clone(),
                dst_chain_id.clone(),
                src_client_id.clone(),
                dst_client_id.clone(),
            );
            if let Some(sender) = sender_cache_a.get(&cache_key) {
                ((*sender).clone(), None)
            } else {
                let (sender, receiver) = SrcRuntime::new_channel();
                sender_cache_a.insert(cache_key, sender.clone());
                (sender, Some(receiver))
            }
        };

        let (dst_sender, m_dst_receiver) = {
            let mutex = build.batch_sender_cache(Target::DstChainTarget::default());
            let mut sender_cache_b = Build::Runtime::acquire_mutex(mutex).await;
            let cache_key = (
                dst_chain_id.clone(),
                src_chain_id.clone(),
                dst_client_id.clone(),
                src_client_id.clone(),
            );
            if let Some(sender) = sender_cache_b.get(&cache_key) {
                ((*sender).clone(), None)
            } else {
                let (sender, receiver) = DstRuntime::new_channel();
                sender_cache_b.insert(cache_key, sender.clone());
                (sender, Some(receiver))
            }
        };

        let relay = InBuilder::build_relay_with_batch(
            build,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_sender,
            dst_sender,
        )
        .await?;

        if let Some(src_receiver) = m_src_receiver {
            relay.clone().spawn_batch_message_worker(
                SourceTarget,
                build.batch_config().clone(),
                src_receiver,
            );
        }

        if let Some(dst_receiver) = m_dst_receiver {
            relay.clone().spawn_batch_message_worker(
                DestinationTarget,
                build.batch_config().clone(),
                dst_receiver,
            );
        }

        Ok(relay)
    }
}
