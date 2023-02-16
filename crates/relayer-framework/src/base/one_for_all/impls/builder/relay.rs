use async_trait::async_trait;

use crate::base::builder::impls::cache::BuildWithCache;
use crate::base::builder::impls::relay::BuildRelayFromChains;
use crate::base::builder::traits::relay::{
    CanBuildRelayAToB, CanBuildRelayAToBFromChains, CanBuildRelayBToA, CanBuildRelayBToAFromChains,
    RelayAToBBuilder, RelayBToABuilder,
};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, OfaBuilder, RelayAToB, RelayBToA,
};
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
        src_client_id: &ClientIdA<Builder>,
        dst_client_id: &ClientIdB<Builder>,
        src_chain: OfaChainWrapper<ChainA<Builder>>,
        dst_chain: OfaChainWrapper<ChainB<Builder>>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Builder>>, Builder::Error> {
        let relay_a_to_b = OfaBuilder::build_relay_a_to_b(
            self.builder.as_ref(),
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await?;

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
        src_client_id: &ClientIdB<Builder>,
        dst_client_id: &ClientIdA<Builder>,
        src_chain: OfaChainWrapper<ChainB<Builder>>,
        dst_chain: OfaChainWrapper<ChainA<Builder>>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Builder>>, Builder::Error> {
        let relay_b_to_a = OfaBuilder::build_relay_b_to_a(
            self.builder.as_ref(),
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await?;

        Ok(OfaRelayWrapper::new(relay_b_to_a))
    }
}

#[async_trait]
impl<Builder> CanBuildRelayAToB for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_relay_a_to_b(
        &self,
        src_chain_id: &ChainIdA<Builder>,
        dst_chain_id: &ChainIdB<Builder>,
        src_client_id: &ClientIdA<Builder>,
        dst_client_id: &ClientIdB<Builder>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Builder>>, Self::Error> {
        <BuildWithCache<BuildRelayFromChains>>::build_relay_a_to_b(
            self,
            src_chain_id,
            dst_chain_id,
            src_client_id,
            dst_client_id,
        )
        .await
    }
}

#[async_trait]
impl<Builder> CanBuildRelayBToA for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_relay_b_to_a(
        &self,
        src_chain_id: &ChainIdB<Builder>,
        dst_chain_id: &ChainIdA<Builder>,
        src_client_id: &ClientIdB<Builder>,
        dst_client_id: &ClientIdA<Builder>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Builder>>, Self::Error> {
        <BuildWithCache<BuildRelayFromChains>>::build_relay_b_to_a(
            self,
            src_chain_id,
            dst_chain_id,
            src_client_id,
            dst_client_id,
        )
        .await
    }
}
