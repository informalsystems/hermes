use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{
    TargetDstChain, TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChain,
    TargetSrcChainId, TargetSrcClientId,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildRelay<Target>: HasBiRelayType + HasErrorType
where
    Target: RelayBuildTarget<Self>,
{
    async fn build_relay(
        &self,
        target: Target,
        src_chain_id: &TargetSrcChainId<Self, Target>,
        dst_chain_id: &TargetDstChainId<Self, Target>,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
    ) -> Result<TargetRelay<Self, Target>, Self::Error>;
}

#[async_trait]
pub trait RelayBuilder<Build, Target>: Async
where
    Build: HasBiRelayType + HasErrorType,
    Target: RelayBuildTarget<Build>,
{
    async fn build_relay(
        build: &Build,
        target: Target,
        src_chain_id: &TargetSrcChainId<Build, Target>,
        dst_chain_id: &TargetDstChainId<Build, Target>,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}

#[async_trait]
pub trait RelayFromChainsBuilder<Build, Target>: Async
where
    Build: HasBiRelayType + HasErrorType,
    Target: RelayBuildTarget<Build>,
{
    async fn build_relay_from_chains(
        build: &Build,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}
