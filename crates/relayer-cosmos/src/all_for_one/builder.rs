use async_trait::async_trait;
use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer_all_in_one::all_for_one::builder::CanBuildAfoBiRelay;
use ibc_relayer_all_in_one::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::builder::OfaBuilderWrapper;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::all_for_one::birelay::AfoCosmosBiRelay;
use crate::contexts::birelay::CosmosBiRelay;
use crate::contexts::builder::CosmosBuilder;

#[async_trait]
pub trait CanBuildAfoCosmosBaseBiRelay: HasErrorType {
    type AfoCosmosBaseBiRelay: AfoCosmosBiRelay;

    async fn build_afo_cosmos_birelay(
        &self,
        chain_id_a: &ChainId,
        chain_id_b: &ChainId,
        client_id_a: &ClientId,
        client_id_b: &ClientId,
    ) -> Result<Self::AfoCosmosBaseBiRelay, Self::Error>;
}

#[async_trait]
impl CanBuildAfoCosmosBaseBiRelay for OfaBuilderWrapper<CosmosBuilder> {
    type AfoCosmosBaseBiRelay = OfaBiRelayWrapper<CosmosBiRelay<BaseChainHandle, BaseChainHandle>>;

    async fn build_afo_cosmos_birelay(
        &self,
        chain_id_a: &ChainId,
        chain_id_b: &ChainId,
        client_id_a: &ClientId,
        client_id_b: &ClientId,
    ) -> Result<Self::AfoCosmosBaseBiRelay, Self::Error> {
        self.build_afo_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}
