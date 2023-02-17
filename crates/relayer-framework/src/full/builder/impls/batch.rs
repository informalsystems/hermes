use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::relay::RelayFromChainsBuilder;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{
    RelayError, TargetDstChain, TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChain,
    TargetSrcChainId, TargetSrcClientId,
};
use crate::base::chain::traits::types::chain_id::HasChainId;
use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::runtime::traits::mutex::{HasMutex, HasRuntimeWithMutex};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::types::aliases::Runtime;
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
impl<Build, InBuilder, Target> RelayFromChainsBuilder<Build, Target> for BuildBatchWorker<InBuilder>
where
    Target: RelayBuildTarget<Build>,
    TargetRelay<Build, Target>: Clone,
    TargetSrcChain<Build, Target>: HasRuntime + HasChainId,
    TargetDstChain<Build, Target>: HasRuntime + HasChainId,
    TargetSrcChainId<Build, Target>: Ord + Clone,
    TargetDstChainId<Build, Target>: Ord + Clone,
    TargetSrcClientId<Build, Target>: Ord + Clone,
    TargetDstClientId<Build, Target>: Ord + Clone,
    InBuilder: RelayWithBatchBuilder<Build, Target>,
    Runtime<TargetSrcChain<Build, Target>>: CanCreateChannels + HasChannelOnceTypes,
    Runtime<TargetDstChain<Build, Target>>: CanCreateChannels + HasChannelOnceTypes,
    Build: HasBiRelayType
        + HasRuntimeWithMutex
        + HasBatchConfig
        + HasErrorType
        + HasBatchSenderCache<Target::SrcChainTarget>
        + HasBatchSenderCache<Target::DstChainTarget>,
    MessageBatchSender<TargetSrcChain<Build, Target>, RelayError<Build>>: Clone,
    MessageBatchSender<TargetDstChain<Build, Target>, RelayError<Build>>: Clone,
    Target::TargetRelay: CanSpawnBatchMessageWorker<SourceTarget>
        + CanSpawnBatchMessageWorker<DestinationTarget>
        + Clone,
{
    async fn build_relay_from_chains(
        build: &Build,
        target: Target,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
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
                let (sender, receiver) = <Runtime<TargetSrcChain<Build, Target>>>::new_channel();
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
                let (sender, receiver) = <Runtime<TargetDstChain<Build, Target>>>::new_channel();
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
