use async_trait::async_trait;

use crate::base::builder::traits::birelay::{BiRelayBuilder, CanBuildBiRelayFromRelays};
use crate::base::builder::traits::relay::{CanBuildRelayAToB, CanBuildRelayBToA};
use crate::std_prelude::*;

pub struct BuildBiRelayFromRelays;

#[async_trait]
impl<Builder> BiRelayBuilder<Builder> for BuildBiRelayFromRelays
where
    Builder: CanBuildBiRelayFromRelays + CanBuildRelayAToB + CanBuildRelayBToA,
{
    async fn build_birelay(builder: &Builder) -> Result<Builder::BiRelay, Builder::Error> {
        let relay_a_to_b = builder.build_relay_a_to_b().await?;
        let relay_b_to_a = builder.build_relay_b_to_a().await?;

        builder
            .build_birelay_from_relays(relay_a_to_b, relay_b_to_a)
            .await
    }
}
