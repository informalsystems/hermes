use core::marker::PhantomData;

use async_trait::async_trait;

use crate::builder::traits::chain::CanBuildChain;
use crate::builder::traits::relay::{RelayBuilder, RelayFromChainsBuilder};
use crate::builder::traits::target::relay::RelayBuildTarget;
use crate::builder::types::aliases::{DstChainTarget, SrcChainTarget};
use crate::builder::types::aliases::{
    TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChainId, TargetSrcClientId,
};
use crate::std_prelude::*;

pub struct BuildRelayFromChains<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<Build, InBuilder, Target> RelayBuilder<Build, Target> for BuildRelayFromChains<InBuilder>
where
    Build:
        CanBuildChain<SrcChainTarget<Build, Target>> + CanBuildChain<DstChainTarget<Build, Target>>,
    InBuilder: RelayFromChainsBuilder<Build, Target>,
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

        InBuilder::build_relay_from_chains(
            build,
            target,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await
    }
}
