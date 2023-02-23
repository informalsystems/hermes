use async_trait::async_trait;
use ibc_relayer_all_in_one::one_for_all::traits::birelay::OfaBiRelayPreset;
use ibc_relayer_all_in_one::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_components::builder::traits::birelay::{CanBuildBiRelay, HasBiRelayType};
use ibc_relayer_components::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use ibc_relayer_components::core::traits::error::HasErrorType;

use crate::all_for_one::birelay::AfoFullBiRelay;
use crate::one_for_all::traits::builder::OfaFullBuilder;
use crate::one_for_all::types::builder::OfaFullBuilderWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAfoFullBiRelay:
    HasBiRelayType<BiRelay = Self::AfoFullBiRelay> + HasErrorType
{
    type AfoFullBiRelay: AfoFullBiRelay;

    async fn build_afo_full_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::AfoFullBiRelay, Self::Error>;
}

#[async_trait]
impl<Context> CanBuildAfoFullBiRelay for Context
where
    Context: CanBuildBiRelay,
    Context::BiRelay: AfoFullBiRelay,
{
    type AfoFullBiRelay = Context::BiRelay;

    async fn build_afo_full_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Context::BiRelay, Context::Error> {
        self.build_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}

#[async_trait]
pub trait CanBuildAfoFullBiRelayFromOfa:
    HasBiRelayType<BiRelay = Self::AfoFullBiRelay> + HasErrorType
{
    type AfoFullBiRelay: AfoFullBiRelay;

    async fn build_afo_full_birelay_from_ofa(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::AfoFullBiRelay, Self::Error>;
}

#[async_trait]
impl<Build> CanBuildAfoFullBiRelayFromOfa for OfaFullBuilderWrapper<Build>
where
    Build: OfaFullBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    type AfoFullBiRelay = OfaBiRelayWrapper<Build::BiRelay>;

    async fn build_afo_full_birelay_from_ofa(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<OfaBiRelayWrapper<Build::BiRelay>, Build::Error> {
        self.build_afo_full_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}
