use core::marker::PhantomData;

use async_trait::async_trait;

use crate::builder::traits::cache::HasRelayCache;
use crate::builder::traits::relay::build::RelayBuilder;
use crate::builder::traits::target::relay::RelayBuildTarget;
use crate::builder::types::aliases::{
    TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChainId, TargetSrcClientId,
};
use crate::core::traits::error::HasErrorType;
use crate::runtime::traits::mutex::HasMutex;
use crate::std_prelude::*;

pub struct BuildRelayWithCache<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<InBuilder, Build, Target> RelayBuilder<Build, Target> for BuildRelayWithCache<InBuilder>
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
