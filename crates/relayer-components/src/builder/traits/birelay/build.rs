use async_trait::async_trait;

use crate::builder::traits::birelay::types::HasBiRelayType;
use crate::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildBiRelay: HasBiRelayType + HasErrorType {
    async fn build_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

#[async_trait]
pub trait BiRelayBuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_birelay(
        builder: &Builder,
        chain_id_a: &ChainIdA<Builder>,
        chain_id_b: &ChainIdB<Builder>,
        client_id_a: &ClientIdA<Builder>,
        client_id_b: &ClientIdB<Builder>,
    ) -> Result<Builder::BiRelay, Builder::Error>;
}
