use async_trait::async_trait;

use crate::base::builder::traits::chain::{CanBuildChainA, CanBuildChainB};
use crate::base::builder::traits::relay::{
    CanBuildRelayAToBFromChains, CanBuildRelayBToAFromChains, RelayAToBBuilder, RelayBToABuilder,
};
use crate::base::builder::types::aliases::{
    ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA,
};
use crate::std_prelude::*;

pub struct BuildRelayFromChains;

#[async_trait]
impl<Builder> RelayAToBBuilder<Builder> for BuildRelayFromChains
where
    Builder: CanBuildChainA + CanBuildChainB + CanBuildRelayAToBFromChains,
{
    async fn build_relay_a_to_b(
        builder: &Builder,
        src_chain_id: &ChainIdA<Builder>,
        dst_chain_id: &ChainIdB<Builder>,
        src_client_id: &ClientIdA<Builder>,
        dst_client_id: &ClientIdB<Builder>,
    ) -> Result<RelayAToB<Builder>, Builder::Error> {
        let src_chain = builder.build_chain_a(src_chain_id).await?;
        let dst_chain = builder.build_chain_b(dst_chain_id).await?;

        builder
            .build_relay_a_to_b_from_chains(src_client_id, dst_client_id, src_chain, dst_chain)
            .await
    }
}

#[async_trait]
impl<Builder> RelayBToABuilder<Builder> for BuildRelayFromChains
where
    Builder: CanBuildChainA + CanBuildChainB + CanBuildRelayBToAFromChains,
{
    async fn build_relay_b_to_a(
        builder: &Builder,
        src_chain_id: &ChainIdB<Builder>,
        dst_chain_id: &ChainIdA<Builder>,
        src_client_id: &ClientIdB<Builder>,
        dst_client_id: &ClientIdA<Builder>,
    ) -> Result<RelayBToA<Builder>, Builder::Error> {
        let src_chain = builder.build_chain_b(src_chain_id).await?;
        let dst_chain = builder.build_chain_a(dst_chain_id).await?;

        builder
            .build_relay_b_to_a_from_chains(src_client_id, dst_client_id, src_chain, dst_chain)
            .await
    }
}
