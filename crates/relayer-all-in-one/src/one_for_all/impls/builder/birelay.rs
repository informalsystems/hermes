use async_trait::async_trait;
use ibc_relayer_components::builder::impls::birelay::BuildBiRelayFromRelays;
use ibc_relayer_components::builder::traits::birelay::build::{BiRelayBuilder, CanBuildBiRelay};
use ibc_relayer_components::builder::traits::birelay::from_relays::CanBuildBiRelayFromRelays;

use crate::one_for_all::traits::builder::{
    ChainIdA, ChainIdB, ClientIdA, ClientIdB, OfaBuilder, RelayAToB, RelayBToA,
};
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Builder> CanBuildBiRelayFromRelays for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    async fn build_birelay_from_relays(
        &self,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Builder>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Builder>>,
    ) -> Result<OfaBiRelayWrapper<Builder::BiRelay>, Builder::Error> {
        let birelay =
            OfaBuilder::build_birelay(self.builder.as_ref(), relay_a_to_b, relay_b_to_a).await?;

        Ok(OfaBiRelayWrapper::new(birelay))
    }
}

#[async_trait]
impl<Builder> CanBuildBiRelay for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    async fn build_birelay(
        &self,
        chain_id_a: &ChainIdA<Builder>,
        chain_id_b: &ChainIdB<Builder>,
        client_id_a: &ClientIdA<Builder>,
        client_id_b: &ClientIdB<Builder>,
    ) -> Result<Self::BiRelay, Self::Error> {
        BuildBiRelayFromRelays::build_birelay(
            self,
            chain_id_a,
            chain_id_b,
            client_id_a,
            client_id_b,
        )
        .await
    }
}
