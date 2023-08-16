use async_trait::async_trait;

use crate::builder::impls::bootstrap::relay::CanBootstrapRelay;
use crate::builder::traits::birelay::build::CanBuildBiRelay;
use crate::builder::traits::birelay::types::HasBiRelayType;
use crate::builder::traits::target::relay::RelayAToBTarget;
use crate::builder::types::aliases::{ChainA, ChainB, ChainIdA, ChainIdB};
use crate::chain::traits::client::create::HasCreateClientOptions;
use crate::core::traits::error::HasErrorType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::two_way::HasTwoWayRelay;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBootstrapBiRelay: HasBiRelayType + HasErrorType
where
    ChainA<Self>: HasCreateClientOptions<ChainB<Self>>,
    ChainB<Self>: HasCreateClientOptions<ChainA<Self>>,
{
    async fn bootstrap_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        payload_options_a: &<ChainA<Self> as HasCreateClientOptions<ChainB<Self>>>::CreateClientPayloadOptions,
        payload_options_b: &<ChainB<Self> as HasCreateClientOptions<ChainA<Self>>>::CreateClientPayloadOptions,
    ) -> Result<Self::BiRelay, Self::Error>;
}

#[async_trait]
impl<Build, BiRelay, RelayAToB, ChainA, ChainB, Error> CanBootstrapBiRelay for Build
where
    Build: HasBiRelayType<BiRelay = BiRelay>
        + HasErrorType<Error = Error>
        + CanBuildBiRelay
        + CanBootstrapRelay<RelayAToBTarget>,
    BiRelay: HasTwoWayRelay<RelayAToB = RelayAToB>,
    RelayAToB: HasRelayChains<SrcChain = ChainA, DstChain = ChainB>,
    ChainA: HasCreateClientOptions<ChainB>,
    ChainB: HasCreateClientOptions<ChainA>,
{
    async fn bootstrap_birelay(
        &self,
        chain_id_a: &ChainA::ChainId,
        chain_id_b: &ChainB::ChainId,
        payload_options_a: &ChainA::CreateClientPayloadOptions,
        payload_options_b: &ChainB::CreateClientPayloadOptions,
    ) -> Result<BiRelay, Error> {
        let relay_a_to_b = self
            .bootstrap_relay(
                RelayAToBTarget,
                chain_id_a,
                chain_id_b,
                payload_options_a,
                payload_options_b,
            )
            .await?;

        let bi_relay = self
            .build_birelay(
                chain_id_a,
                chain_id_b,
                relay_a_to_b.src_client_id(),
                relay_a_to_b.dst_client_id(),
            )
            .await?;

        Ok(bi_relay)
    }
}
