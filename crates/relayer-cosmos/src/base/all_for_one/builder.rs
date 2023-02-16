use async_trait::async_trait;
use ibc_relayer_framework::base::builder::traits::birelay::CanBuildAfoBaseBiRelay;
use ibc_relayer_framework::base::core::traits::error::HasErrorType;
use ibc_relayer_framework::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use ibc_relayer_framework::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::builder::OfaBuilderWrapper;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::base::all_for_one::birelay::AfoCosmosBaseBiRelay;
use crate::base::traits::builder::CosmosBuilder;
use crate::base::types::birelay::CosmosBiRelayWrapper;
use crate::base::types::builder::CosmosBuilderWrapper;

#[async_trait]
pub trait CanBuildAfoCosmosBaseBiRelay: HasErrorType {
    type AfoCosmosBaseBiRelay: AfoCosmosBaseBiRelay;

    async fn build_afo_cosmos_base_birelay(
        &self,
        chain_id_a: &ChainId,
        chain_id_b: &ChainId,
        client_id_a: &ClientId,
        client_id_b: &ClientId,
    ) -> Result<Self::AfoCosmosBaseBiRelay, Self::Error>;
}

#[async_trait]
impl<Builder> CanBuildAfoCosmosBaseBiRelay for OfaBuilderWrapper<CosmosBuilderWrapper<Builder>>
where
    Builder: CosmosBuilder,
    Builder::Preset: OfaBiRelayPreset<CosmosBiRelayWrapper<Builder::BiRelay>>,
{
    type AfoCosmosBaseBiRelay = OfaBiRelayWrapper<CosmosBiRelayWrapper<Builder::BiRelay>>;

    async fn build_afo_cosmos_base_birelay(
        &self,
        chain_id_a: &ChainId,
        chain_id_b: &ChainId,
        client_id_a: &ClientId,
        client_id_b: &ClientId,
    ) -> Result<Self::AfoCosmosBaseBiRelay, Self::Error> {
        self.build_afo_base_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}
