use async_trait::async_trait;

use crate::base::all_for_one::birelay::AfoBaseBiRelay;
use crate::base::builder::traits::birelay::{CanBuildBiRelay, HasBiRelayType};
use crate::base::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::traits::builder::OfaBuilder;
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAfoBaseBiRelay:
    HasBiRelayType<BiRelay = Self::AfoBaseBiRelay> + HasErrorType
{
    type AfoBaseBiRelay: AfoBaseBiRelay;

    async fn build_afo_base_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::AfoBaseBiRelay, Self::Error>;
}

#[async_trait]
impl<Build> CanBuildAfoBaseBiRelay for Build
where
    Build: CanBuildBiRelay,
    Build::BiRelay: AfoBaseBiRelay,
{
    type AfoBaseBiRelay = Build::BiRelay;

    async fn build_afo_base_birelay(
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
pub trait CanBuildAfoBaseBiRelayFromOfa:
    HasBiRelayType<BiRelay = Self::AfoBaseBiRelay> + HasErrorType
{
    type AfoBaseBiRelay: AfoBaseBiRelay;

    async fn build_afo_base_birelay_from_ofa(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::AfoBaseBiRelay, Self::Error>;
}

#[async_trait]
impl<Build> CanBuildAfoBaseBiRelayFromOfa for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
    Build::Preset: OfaBiRelayPreset<Build::BiRelay>,
{
    type AfoBaseBiRelay = OfaBiRelayWrapper<Build::BiRelay>;

    async fn build_afo_base_birelay_from_ofa(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<OfaBiRelayWrapper<Build::BiRelay>, Build::Error> {
        self.build_afo_base_birelay(chain_id_a, chain_id_b, client_id_a, client_id_b)
            .await
    }
}
