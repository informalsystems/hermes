use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::builder::traits::chain::{CanBuildChainA, CanBuildChainB};
use crate::base::builder::traits::relay::{
    RelayAToBBuilder, RelayAToBFromChainsBuilder, RelayBToABuilder, RelayBToAFromChainsBuilder,
};
use crate::base::builder::types::aliases::{
    ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA,
};
use crate::std_prelude::*;

pub struct BuildRelayFromChains<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<Build, InBuilder> RelayAToBBuilder<Build> for BuildRelayFromChains<InBuilder>
where
    Build: CanBuildChainA + CanBuildChainB,
    InBuilder: RelayAToBFromChainsBuilder<Build>,
{
    async fn build_relay_a_to_b(
        build: &Build,
        src_chain_id: &ChainIdA<Build>,
        dst_chain_id: &ChainIdB<Build>,
        src_client_id: &ClientIdA<Build>,
        dst_client_id: &ClientIdB<Build>,
    ) -> Result<RelayAToB<Build>, Build::Error> {
        let src_chain = build.build_chain_a(src_chain_id).await?;
        let dst_chain = build.build_chain_b(dst_chain_id).await?;

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

#[async_trait]
impl<Build, InBuilder> RelayBToABuilder<Build> for BuildRelayFromChains<InBuilder>
where
    Build: CanBuildChainA + CanBuildChainB,
    InBuilder: RelayBToAFromChainsBuilder<Build>,
{
    async fn build_relay_b_to_a(
        build: &Build,
        src_chain_id: &ChainIdB<Build>,
        dst_chain_id: &ChainIdA<Build>,
        src_client_id: &ClientIdB<Build>,
        dst_client_id: &ClientIdA<Build>,
    ) -> Result<RelayBToA<Build>, Build::Error> {
        let src_chain = build.build_chain_b(src_chain_id).await?;
        let dst_chain = build.build_chain_a(dst_chain_id).await?;

        InBuilder::build_relay_b_to_a_from_chains(
            build,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await
    }
}
