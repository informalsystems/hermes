use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::builder::traits::chain::CanBuildChain;
use crate::base::builder::traits::relay::{RelayBuilder, RelayFromChainsBuilder};
use crate::base::builder::traits::target::relay::HasRelayBuildTarget;
use crate::base::builder::types::aliases::{DstChainTarget, SrcChainTarget};
use crate::base::builder::types::aliases::{
    TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChainId, TargetSrcClientId,
};
use crate::std_prelude::*;

pub struct BuildRelayFromChains<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<Build, InBuilder, Target> RelayBuilder<Build, Target> for BuildRelayFromChains<InBuilder>
where
    Build: HasRelayBuildTarget<Target>
        + CanBuildChain<SrcChainTarget<Build, Target>>
        + CanBuildChain<DstChainTarget<Build, Target>>,
    InBuilder: RelayFromChainsBuilder<Build, Target>,
{
    async fn build_relay(
        build: &Build,
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

        InBuilder::build_relay_a_to_b_from_chains(
            build,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await
    }
}
