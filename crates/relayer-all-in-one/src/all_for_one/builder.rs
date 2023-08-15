use async_trait::async_trait;
use ibc_relayer_components::builder::traits::birelay::build::CanBuildBiRelay;
use ibc_relayer_components::builder::traits::birelay::types::HasBiRelayType;
use ibc_relayer_components::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::all_for_one::birelay::AfoBiRelay;
use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAfoBiRelay: HasBiRelayType<BiRelay = Self::AfoBiRelay> + HasErrorType {
    type AfoBiRelay: AfoBiRelay;

    async fn build_afo_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::AfoBiRelay, Self::Error>;
}

#[async_trait]
impl<Build> CanBuildAfoBiRelay for Build
where
    Build: CanBuildBiRelay,
    Build::BiRelay: AfoBiRelay,
{
    type AfoBiRelay = Build::BiRelay;

    async fn build_afo_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Build::BiRelay, Build::Error> {
        self.build_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}

#[async_trait]
pub trait CanBuildAfoBiRelayFromOfa:
    HasBiRelayType<BiRelay = Self::AfoBiRelay> + HasErrorType
{
    type AfoBiRelay: AfoBiRelay;

    async fn build_afo_birelay_from_ofa(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::AfoBiRelay, Self::Error>;
}

// #[async_trait]
// impl<Build> CanBuildAfoBiRelayFromOfa for OfaBuilderWrapper<Build>
// where
//     Build: OfaBuilder,
// {
//     type AfoBiRelay = OfaBiRelayWrapper<Build::BiRelay>;

//     async fn build_afo_birelay_from_ofa(
//         &self,
//         chain_id_a: &ChainIdA<Self>,
//         chain_id_b: &ChainIdB<Self>,
//         client_id_a: &ClientIdA<Self>,
//         client_id_b: &ClientIdB<Self>,
//     ) -> Result<OfaBiRelayWrapper<Build::BiRelay>, Build::Error> {
//         self.build_afo_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
//             .await
//     }
// }
