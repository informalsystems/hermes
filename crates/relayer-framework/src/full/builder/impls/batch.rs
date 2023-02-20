use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::relay::RelayFromChainsBuilder;
use crate::base::builder::traits::target::chain::ChainBuildTarget;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{
    CounterpartyChainId, CounterpartyClientId, RelayError, TargetChain, TargetChainId,
    TargetChainRuntime, TargetClientId,
};
use crate::base::chain::traits::types::chain_id::HasChainId;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::mutex::{HasMutex, HasRuntimeWithMutex};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::traits::config::HasBatchConfig;
use crate::full::batch::types::aliases::{MessageBatchReceiver, MessageBatchSender};
use crate::full::batch::worker::CanSpawnBatchMessageWorker;
use crate::full::builder::traits::cache::HasBatchSenderCache;
use crate::full::builder::traits::relay::RelayBuilderWithBatch;
use crate::full::runtime::traits::channel::{CanCreateChannels, HasChannelTypes};
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;
use crate::std_prelude::*;

pub struct BuildBatchWorker<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<Build, InBuilder, Target, Relay, SrcChain, DstChain, SrcRuntime, DstRuntime>
    RelayFromChainsBuilder<Build, Target> for BuildBatchWorker<InBuilder>
where
    InBuilder: RelayBuilderWithBatch<Build, Target>,
    Build: HasBiRelayType + HasRuntimeWithMutex + HasBatchConfig + HasErrorType,
    Build:
        CanBuildBatchChannel<Target::SrcChainTarget> + CanBuildBatchChannel<Target::DstChainTarget>,
    Target: RelayBuildTarget<Build, TargetRelay = Relay>,
    Relay: HasRelayTypes<SrcChain = SrcChain, DstChain = DstChain, Error = RelayError<Build>>,
    Relay: CanSpawnBatchMessageWorker<SourceTarget>
        + CanSpawnBatchMessageWorker<DestinationTarget>
        + Clone,
    SrcChain: HasIbcChainTypes<DstChain>,
    DstChain: HasIbcChainTypes<SrcChain>,
    SrcChain: HasRuntime<Runtime = SrcRuntime> + HasChainId,
    DstChain: HasRuntime<Runtime = DstRuntime> + HasChainId,
    SrcRuntime: HasChannelTypes + HasChannelOnceTypes,
    DstRuntime: HasChannelTypes + HasChannelOnceTypes,
    MessageBatchSender<SrcChain, Relay::Error>: Clone,
    MessageBatchSender<DstChain, Relay::Error>: Clone,
{
    async fn build_relay_from_chains(
        build: &Build,
        target: Target,
        src_client_id: &SrcChain::ClientId,
        dst_client_id: &DstChain::ClientId,
        src_chain: SrcChain,
        dst_chain: DstChain,
    ) -> Result<Target::TargetRelay, Build::Error> {
        let src_chain_id = src_chain.chain_id();
        let dst_chain_id = dst_chain.chain_id();

        let (src_sender, m_src_receiver) = build
            .build_batch_channel(
                Target::SrcChainTarget::default(),
                src_chain_id,
                dst_chain_id,
                src_client_id,
                dst_client_id,
            )
            .await?;

        let (dst_sender, m_dst_receiver) = build
            .build_batch_channel(
                Target::DstChainTarget::default(),
                dst_chain_id,
                src_chain_id,
                dst_client_id,
                src_client_id,
            )
            .await?;

        let relay = InBuilder::build_relay_with_batch(
            build,
            target,
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

#[async_trait]
trait CanBuildBatchChannel<Target>: HasBiRelayType + HasErrorType
where
    Target: ChainBuildTarget<Self>,
    TargetChain<Self, Target>: HasRuntime,
    TargetChainRuntime<Self, Target>: HasChannelTypes + HasChannelOnceTypes,
{
    async fn build_batch_channel(
        &self,
        target: Target,
        chain_id: &TargetChainId<Self, Target>,
        counterparty_chain_id: &CounterpartyChainId<Self, Target>,
        client_id: &TargetClientId<Self, Target>,
        counterparty_client_id: &CounterpartyClientId<Self, Target>,
    ) -> Result<
        (
            MessageBatchSender<TargetChain<Self, Target>, RelayError<Self>>,
            Option<MessageBatchReceiver<TargetChain<Self, Target>, RelayError<Self>>>,
        ),
        Self::Error,
    >;
}

#[async_trait]
impl<Build, Target, Chain, Counterparty, Runtime> CanBuildBatchChannel<Target> for Build
where
    Build: HasBiRelayType + HasErrorType,
    Target: ChainBuildTarget<Self, TargetChain = Chain, CounterpartyChain = Counterparty>,
    Chain: HasIbcChainTypes<Counterparty> + HasRuntime<Runtime = Runtime>,
    Counterparty: HasIbcChainTypes<Chain>,
    Runtime: CanCreateChannels + HasChannelOnceTypes,
    Build: HasBatchSenderCache<Target, RelayError<Build>>,
    Chain::ChainId: Ord + Clone,
    Counterparty::ChainId: Ord + Clone,
    Chain::ClientId: Ord + Clone,
    Counterparty::ClientId: Ord + Clone,
    MessageBatchSender<Chain, RelayError<Self>>: Clone,
{
    async fn build_batch_channel(
        &self,
        target: Target,
        chain_id: &Chain::ChainId,
        counterparty_chain_id: &Counterparty::ChainId,
        client_id: &Chain::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
    ) -> Result<
        (
            MessageBatchSender<Chain, RelayError<Self>>,
            Option<MessageBatchReceiver<Chain, RelayError<Self>>>,
        ),
        Self::Error,
    > {
        let mutex = self.batch_sender_cache(target);

        let mut sender_cache = Build::Runtime::acquire_mutex(mutex).await;

        let cache_key = (
            chain_id.clone(),
            counterparty_chain_id.clone(),
            client_id.clone(),
            counterparty_client_id.clone(),
        );

        if let Some(sender) = sender_cache.get(&cache_key) {
            Ok(((*sender).clone(), None))
        } else {
            let (sender, receiver) = Runtime::new_channel();
            sender_cache.insert(cache_key, sender.clone());
            Ok((sender, Some(receiver)))
        }
    }
}
