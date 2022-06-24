use async_trait::async_trait;

use crate::traits::chain_context::ChainContext;
use crate::types::aliases::{Height, Timestamp};

pub trait ChainStatus<Chain: ChainContext> {
    fn height(&self) -> Height<Chain>;

    fn timestamp(&self) -> Timestamp<Chain>;
}

#[async_trait]
pub trait ChainStatusQuerier: ChainContext {
    type ChainStatus: ChainStatus<Self>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}
