use async_trait::async_trait;

use crate::build::traits::components::chain_builder::CanBuildChain;
use crate::build::traits::components::relay_builder::RelayBuilder;
use crate::build::traits::components::relay_from_chains_builder::CanBuildRelayFromChains;
use crate::build::traits::target::relay::RelayBuildTarget;
use crate::build::types::aliases::{DstChainTarget, SrcChainTarget};
use crate::build::types::aliases::{
    TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChainId, TargetSrcClientId,
};
use crate::std_prelude::*;

pub struct BuildRelayFromChains;

#[async_trait]
impl<Build, Target> RelayBuilder<Build, Target> for BuildRelayFromChains
where
    Build: CanBuildChain<SrcChainTarget<Build, Target>>
        + CanBuildChain<DstChainTarget<Build, Target>>
        + CanBuildRelayFromChains<Target>,
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
        let src_chain = build
            .build_chain(<SrcChainTarget<Build, Target>>::default(), src_chain_id)
            .await?;

        let dst_chain = build
            .build_chain(<DstChainTarget<Build, Target>>::default(), dst_chain_id)
            .await?;

        build
            .build_relay_from_chains(target, src_client_id, dst_client_id, src_chain, dst_chain)
            .await
    }
}
