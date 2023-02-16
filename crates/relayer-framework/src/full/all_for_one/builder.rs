use async_trait::async_trait;

use crate::base::builder::traits::birelay::{CanBuildBiRelay, HasBiRelayType};
use crate::base::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use crate::base::core::traits::error::HasErrorType;
use crate::full::all_for_one::birelay::AfoFullBiRelay;
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
