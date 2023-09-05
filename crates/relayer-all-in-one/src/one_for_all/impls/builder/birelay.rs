use async_trait::async_trait;
use ibc_relayer_components::builder::traits::components::birelay_from_relay_builder::BiRelayFromRelayBuilder;

use crate::one_for_all::traits::builder::{OfaBuilder, RelayAToB, RelayBToA};
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Build> BiRelayFromRelayBuilder<OfaBuilderWrapper<Build>> for OfaComponents
where
    Build: OfaBuilder,
{
    async fn build_birelay_from_relays(
        build: &OfaBuilderWrapper<Build>,
        relay_a_to_b: OfaRelayWrapper<RelayAToB<Build>>,
        relay_b_to_a: OfaRelayWrapper<RelayBToA<Build>>,
    ) -> Result<OfaBiRelayWrapper<Build::BiRelay>, Build::Error> {
        let birelay =
            OfaBuilder::build_birelay(build.builder.as_ref(), relay_a_to_b, relay_b_to_a).await?;

        Ok(OfaBiRelayWrapper::new(birelay))
    }
}
