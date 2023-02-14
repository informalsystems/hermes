use async_trait::async_trait;

use crate::base::builder::impls::birelay::BuildBiRelayFromRelays;
use crate::base::builder::traits::birelay::{
    BiRelayBuilder, CanBuildBiRelay, CanBuildBiRelayFromRelays,
};
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::{OfaBuilder, RelayAToB, RelayBToA};
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Builder> CanBuildBiRelayFromRelays for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
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
    Builder::Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    async fn build_birelay(&self) -> Result<Self::BiRelay, Self::Error> {
        BuildBiRelayFromRelays::build_birelay(self).await
    }
}
