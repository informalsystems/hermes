use alloc::collections::BTreeMap;
use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::builder::TargetBuilder;
use crate::base::builder::types::aliases::{ChainA, ChainB, RelayAToB, RelayBToA};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;

pub struct BuildWithCache;

// pub struct BuildWithCache<CacheFetcher, InBuilder>(pub PhantomData<(CacheFetcher, InBuilder)>);

// pub type CacheMutex<Runtime, Id, Target> = <Runtime as HasMutex>::Mutex<BTreeMap<Id, Target>>;

// pub trait BuildCacheFetcher<Context, Target>: Async
// where
//     Target: Async,
//     Context: HasRuntime,
//     Context::Runtime: HasMutex,
// {
//     type Id: Ord + Async;

//     fn get_target_id(context: &Context) -> Self::Id;

//     fn get_cache_mutex(context: &Context) -> &CacheMutex<Context::Runtime, Self::Id, Target>;
// }

// #[async_trait]
// impl<CacheFetcher, InBuilder, Runtime, Context, Target> TargetBuilder<Context, Target>
//     for BuildWithCache<CacheFetcher, InBuilder>
// where
//     Target: Clone + Async,
//     Context: HasRuntime<Runtime = Runtime> + HasErrorType,
//     Runtime: HasMutex,
//     InBuilder: TargetBuilder<Context, Target>,
//     CacheFetcher: BuildCacheFetcher<Context, Target>,
// {
//     async fn build_target(context: &Context) -> Result<Target, Context::Error> {
//         let target_id = CacheFetcher::get_target_id(context);

//         let mutex = CacheFetcher::get_cache_mutex(context);

//         let mut cache = Runtime::acquire_mutex(mutex).await;

//         if let Some(target) = cache.get(&target_id) {
//             Ok(target.clone())
//         } else {
//             let target = InBuilder::build_target(context).await?;

//             cache.insert(target_id, target.clone());

//             Ok(target)
//         }
//     }
// }
