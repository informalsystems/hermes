use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::cache::{HasChainCache, HasRelayCache};
use crate::base::builder::traits::chain::ChainBuilder;
use crate::base::builder::traits::relay::RelayBuilder;
use crate::base::builder::traits::target::chain::ChainBuildTarget;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{
    TargetChain, TargetChainId, TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChainId,
    TargetSrcClientId,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::std_prelude::*;

pub struct BuildWithCache<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<InBuilder, Build, Target> ChainBuilder<Build, Target> for BuildWithCache<InBuilder>
where
    TargetChain<Build, Target>: Clone,
    TargetChainId<Build, Target>: Ord + Clone,
    Build: HasChainCache<Target> + HasErrorType,
    InBuilder: ChainBuilder<Build, Target>,
    Target: ChainBuildTarget<Build>,
{
    async fn build_chain(
        build: &Build,
        target: Target,
        chain_id: &TargetChainId<Build, Target>,
    ) -> Result<TargetChain<Build, Target>, Build::Error> {
        let mut cache = Build::Runtime::acquire_mutex(build.chain_cache()).await;

        if let Some(chain) = cache.get(chain_id) {
            Ok(chain.clone())
        } else {
            let chain = InBuilder::build_chain(build, target, chain_id).await?;
            cache.insert(chain_id.clone(), chain.clone());

            Ok(chain)
        }
    }
}

#[async_trait]
impl<InBuilder, Build, Target> RelayBuilder<Build, Target> for BuildWithCache<InBuilder>
where
    TargetSrcChainId<Build, Target>: Ord + Clone,
    TargetDstChainId<Build, Target>: Ord + Clone,
    TargetSrcClientId<Build, Target>: Ord + Clone,
    TargetDstClientId<Build, Target>: Ord + Clone,
    TargetRelay<Build, Target>: Clone,
    Build: HasRelayCache<Target> + HasErrorType,
    InBuilder: RelayBuilder<Build, Target>,
    Target: RelayBuildTarget<Build>,
{
    async fn build_relay(
        build: &Build,
        target: Target,
        src_chain_id: &TargetSrcChainId<Build, Target>,
        dst_chain_id: &TargetDstChainId<Build, Target>,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error> {
        let relay_id = (
            src_chain_id.clone(),
            dst_chain_id.clone(),
            src_client_id.clone(),
            dst_client_id.clone(),
        );

        let mut cache = Build::Runtime::acquire_mutex(build.relay_cache()).await;

        if let Some(relay) = cache.get(&relay_id) {
            Ok(relay.clone())
        } else {
            let relay = InBuilder::build_relay(
                build,
                target,
                src_chain_id,
                dst_chain_id,
                src_client_id,
                dst_client_id,
            )
            .await?;
            cache.insert(relay_id, relay.clone());

            Ok(relay)
        }
    }
}
