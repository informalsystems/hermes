use async_trait::async_trait;

use crate::base::builder::traits::relay::{
    CanBuildRelayAToBFromChains, CanBuildRelayBToAFromChains,
};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{ChainA, ChainB, OfaBuilder, RelayAToB, RelayBToA};
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Builder> CanBuildRelayAToBFromChains for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_relay_a_to_b_from_chains(
        &self,
        chain_a: OfaChainWrapper<ChainA<Builder>>,
        chain_b: OfaChainWrapper<ChainB<Builder>>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Builder>>, Builder::Error> {
        let relay_a_to_b = self.builder.build_relay_a_to_b(chain_a, chain_b).await?;

        Ok(OfaRelayWrapper::new(relay_a_to_b))
    }
}

#[async_trait]
impl<Builder> CanBuildRelayBToAFromChains for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_relay_b_to_a_from_chains(
        &self,
        chain_b: OfaChainWrapper<ChainB<Builder>>,
        chain_a: OfaChainWrapper<ChainA<Builder>>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Builder>>, Builder::Error> {
        let relay_b_to_a = self.builder.build_relay_b_to_a(chain_b, chain_a).await?;

        Ok(OfaRelayWrapper::new(relay_b_to_a))
    }
}
