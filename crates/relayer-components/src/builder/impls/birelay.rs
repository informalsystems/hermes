use async_trait::async_trait;

use crate::builder::traits::birelay::{BiRelayBuilder, CanBuildBiRelayFromRelays};
use crate::builder::traits::relay::build::CanBuildRelay;
use crate::builder::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use crate::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use crate::std_prelude::*;

pub struct BuildBiRelayFromRelays;

#[async_trait]
impl<Builder> BiRelayBuilder<Builder> for BuildBiRelayFromRelays
where
    Builder:
        CanBuildBiRelayFromRelays + CanBuildRelay<RelayAToBTarget> + CanBuildRelay<RelayBToATarget>,
{
    async fn build_birelay(
        builder: &Builder,
        chain_id_a: &ChainIdA<Builder>,
        chain_id_b: &ChainIdB<Builder>,
        client_id_a: &ClientIdA<Builder>,
        client_id_b: &ClientIdB<Builder>,
    ) -> Result<Builder::BiRelay, Builder::Error> {
        let relay_a_to_b = builder
            .build_relay(
                RelayAToBTarget,
                chain_id_a,
                chain_id_b,
                client_id_a,
                client_id_b,
            )
            .await?;

        let relay_b_to_a = builder
            .build_relay(
                RelayBToATarget,
                chain_id_b,
                chain_id_a,
                client_id_b,
                client_id_a,
            )
            .await?;

        builder
            .build_birelay_from_relays(relay_a_to_b, relay_b_to_a)
            .await
    }
}
