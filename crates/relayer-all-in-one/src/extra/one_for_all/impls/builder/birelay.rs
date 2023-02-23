use async_trait::async_trait;
use ibc_relayer_components::builder::impls::birelay::BuildBiRelayFromRelays;
use ibc_relayer_components::builder::traits::birelay::{
    BiRelayBuilder, CanBuildBiRelay, CanBuildBiRelayFromRelays,
};

use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{
    ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA,
};
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::extra::one_for_all::traits::builder::OfaFullBuilder;
use crate::extra::one_for_all::types::builder::OfaFullBuilderWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Builder> CanBuildBiRelayFromRelays for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_birelay_from_relays(
        &self,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Builder>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Builder>>,
    ) -> Result<OfaBiRelayWrapper<Builder::BiRelay>, Builder::Error> {
        let birelay =
            OfaFullBuilder::build_birelay(self.builder.as_ref(), relay_a_to_b, relay_b_to_a)
                .await?;

        Ok(OfaBiRelayWrapper::new(birelay))
    }
}

#[async_trait]
impl<Builder> CanBuildBiRelay for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
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
