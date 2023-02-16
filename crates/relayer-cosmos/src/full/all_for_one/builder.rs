use async_trait::async_trait;
use ibc_relayer_framework::base::core::traits::error::HasErrorType;
use ibc_relayer_framework::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use ibc_relayer_framework::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::builder::OfaBuilderWrapper;
use ibc_relayer_framework::full::all_for_one::builder::CanBuildAfoFullBiRelay;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::base::traits::builder::{ChainA, ChainB, CosmosBuilder, RelayAToB, RelayBToA};
use crate::base::types::birelay::CosmosBiRelayWrapper;
use crate::base::types::builder::CosmosBuilderWrapper;
use crate::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::traits::relay::CosmosFullRelay;

#[async_trait]
pub trait CanBuildAfoCosmosFullBiRelay: HasErrorType {
    type AfoCosmosFullBiRelay: AfoCosmosFullBiRelay;

    async fn build_afo_cosmos_full_birelay(
        &self,
        chain_id_a: &ChainId,
        chain_id_b: &ChainId,
        client_id_a: &ClientId,
        client_id_b: &ClientId,
    ) -> Result<Self::AfoCosmosFullBiRelay, Self::Error>;
}

#[async_trait]
impl<Builder> CanBuildAfoCosmosFullBiRelay for OfaBuilderWrapper<CosmosBuilderWrapper<Builder>>
where
    Builder: CosmosBuilder,
    ChainA<Builder>: CosmosFullChain,
    ChainB<Builder>: CosmosFullChain,
    RelayAToB<Builder>: CosmosFullRelay,
    RelayBToA<Builder>: CosmosFullRelay,
    Builder::Preset: OfaBiRelayPreset<CosmosBiRelayWrapper<Builder::BiRelay>>,
{
    type AfoCosmosFullBiRelay = OfaBiRelayWrapper<CosmosBiRelayWrapper<Builder::BiRelay>>;

    async fn build_afo_cosmos_full_birelay(
        &self,
        chain_id_a: &ChainId,
        chain_id_b: &ChainId,
        client_id_a: &ClientId,
        client_id_b: &ClientId,
    ) -> Result<Self::AfoCosmosFullBiRelay, Self::Error> {
        self.build_afo_full_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}
