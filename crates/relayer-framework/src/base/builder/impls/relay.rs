use async_trait::async_trait;

use crate::base::builder::traits::chain::{CanBuildChainA, CanBuildChainB};
use crate::base::builder::traits::relay::{
    CanBuildRelayAToBFromChains, CanBuildRelayBToAFromChains, RelayAToBBuilder, RelayBToABuilder,
};
use crate::base::builder::types::aliases::{RelayAToB, RelayBToA};
use crate::std_prelude::*;

pub struct BuildRelayFromChains;

#[async_trait]
impl<Builder> RelayAToBBuilder<Builder> for BuildRelayFromChains
where
    Builder: CanBuildChainA + CanBuildChainB + CanBuildRelayAToBFromChains,
{
    async fn build_relay_a_to_b(builder: &Builder) -> Result<RelayAToB<Builder>, Builder::Error> {
        let chain_a = builder.build_chain_a().await?;
        let chain_b = builder.build_chain_b().await?;

        builder
            .build_relay_a_to_b_from_chains(chain_a, chain_b)
            .await
    }
}

#[async_trait]
impl<Builder> RelayBToABuilder<Builder> for BuildRelayFromChains
where
    Builder: CanBuildChainA + CanBuildChainB + CanBuildRelayBToAFromChains,
{
    async fn build_relay_b_to_a(builder: &Builder) -> Result<RelayBToA<Builder>, Builder::Error> {
        let chain_b = builder.build_chain_b().await?;
        let chain_a = builder.build_chain_a().await?;

        builder
            .build_relay_b_to_a_from_chains(chain_b, chain_a)
            .await
    }
}
