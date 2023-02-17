// use async_trait::async_trait;
// use core::marker::PhantomData;

// use crate::base::builder::traits::birelay::HasBiRelayType;
// use crate::base::builder::traits::relay::RelayAToBFromChainsBuilder;
// use crate::base::builder::types::aliases::{
//     ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayError,
// };
// use crate::base::chain::traits::types::chain_id::HasChainId;
// use crate::base::core::traits::error::HasErrorType;
// use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
// use crate::base::runtime::traits::mutex::{HasMutex, HasRuntimeWithMutex};
// use crate::base::runtime::traits::runtime::HasRuntime;
// use crate::base::runtime::types::aliases::Runtime;
// use crate::full::batch::traits::config::HasBatchConfig;
// use crate::full::batch::types::aliases::MessageBatchSender;
// use crate::full::batch::worker::CanSpawnBatchMessageWorker;
// use crate::full::builder::traits::cache::{HasChainABatchSenderCache, HasChainBBatchSenderCache};
// use crate::full::builder::traits::relay::RelayAToBWithBatchBuilder;
// use crate::full::runtime::traits::channel::CanCreateChannels;
// use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;
// use crate::std_prelude::*;

// pub struct BuildBatchWorker<InBuilder>(pub PhantomData<InBuilder>);

// #[async_trait]
// impl<Build, InBuilder> RelayAToBFromChainsBuilder<Build> for BuildBatchWorker<InBuilder>
// where
//     ChainA<Build>: HasRuntime + HasChainId,
//     ChainB<Build>: HasRuntime + HasChainId,
//     ChainIdA<Build>: Ord + Clone,
//     ChainIdB<Build>: Ord + Clone,
//     ClientIdA<Build>: Ord + Clone,
//     ClientIdB<Build>: Ord + Clone,
//     InBuilder: RelayAToBWithBatchBuilder<Build>,
//     Build: HasBiRelayType + HasRuntimeWithMutex + HasBatchConfig + HasErrorType,
//     Runtime<ChainA<Build>>: CanCreateChannels + HasChannelOnceTypes,
//     Runtime<ChainB<Build>>: CanCreateChannels + HasChannelOnceTypes,
//     Build: HasChainABatchSenderCache + HasChainBBatchSenderCache,
//     MessageBatchSender<ChainA<Build>, RelayError<Build>>: Clone,
//     MessageBatchSender<ChainB<Build>, RelayError<Build>>: Clone,
//     RelayAToB<Build>: CanSpawnBatchMessageWorker<SourceTarget>
//         + CanSpawnBatchMessageWorker<DestinationTarget>
//         + Clone,
// {
//     async fn build_relay_a_to_b_from_chains(
//         build: &Build,
//         src_client_id: &ClientIdA<Build>,
//         dst_client_id: &ClientIdB<Build>,
//         src_chain: ChainA<Build>,
//         dst_chain: ChainB<Build>,
//     ) -> Result<RelayAToB<Build>, Build::Error> {
//         let src_chain_id = src_chain.chain_id();
//         let dst_chain_id = dst_chain.chain_id();

//         let (src_sender, m_src_receiver) = {
//             let mutex = build.batch_sender_cache_a();
//             let mut sender_cache_a = Build::Runtime::acquire_mutex(mutex).await;
//             let cache_key = (
//                 src_chain_id.clone(),
//                 dst_chain_id.clone(),
//                 src_client_id.clone(),
//                 dst_client_id.clone(),
//             );
//             if let Some(sender) = sender_cache_a.get(&cache_key) {
//                 ((*sender).clone(), None)
//             } else {
//                 let (sender, receiver) = <Runtime<ChainA<Build>>>::new_channel();
//                 sender_cache_a.insert(cache_key, sender.clone());
//                 (sender, Some(receiver))
//             }
//         };

//         let (dst_sender, m_dst_receiver) = {
//             let mutex = build.batch_sender_cache_b();
//             let mut sender_cache_b = Build::Runtime::acquire_mutex(mutex).await;
//             let cache_key = (
//                 dst_chain_id.clone(),
//                 src_chain_id.clone(),
//                 dst_client_id.clone(),
//                 src_client_id.clone(),
//             );
//             if let Some(sender) = sender_cache_b.get(&cache_key) {
//                 ((*sender).clone(), None)
//             } else {
//                 let (sender, receiver) = <Runtime<ChainB<Build>>>::new_channel();
//                 sender_cache_b.insert(cache_key, sender.clone());
//                 (sender, Some(receiver))
//             }
//         };

//         let relay = InBuilder::build_relay_a_to_b_with_batch(
//             build,
//             src_client_id,
//             dst_client_id,
//             src_chain,
//             dst_chain,
//             src_sender,
//             dst_sender,
//         )
//         .await?;

//         if let Some(src_receiver) = m_src_receiver {
//             relay.clone().spawn_batch_message_worker(
//                 SourceTarget,
//                 build.batch_config().clone(),
//                 src_receiver,
//             );
//         }

//         if let Some(dst_receiver) = m_dst_receiver {
//             relay.clone().spawn_batch_message_worker(
//                 DestinationTarget,
//                 build.batch_config().clone(),
//                 dst_receiver,
//             );
//         }

//         Ok(relay)
//     }
// }
