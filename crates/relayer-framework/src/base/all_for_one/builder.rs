use async_trait::async_trait;

use crate::base::all_for_one::birelay::AfoBaseBiRelay;
use crate::base::builder::traits::birelay::{CanBuildBiRelay, HasBiRelayType};
use crate::base::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use crate::base::core::traits::error::HasErrorType;
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
impl<Context> CanBuildAfoBaseBiRelay for Context
where
    Context: CanBuildBiRelay,
    Context::BiRelay: AfoBaseBiRelay,
{
    type AfoBaseBiRelay = Context::BiRelay;

    async fn build_afo_base_birelay(
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
