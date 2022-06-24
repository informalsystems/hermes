use async_trait::async_trait;

use crate::traits::chain_context::ChainContext;
use crate::types::aliases::{Height, Timestamp};

pub struct ChainStatus<Chain: ChainContext> {
    pub height: Height<Chain>,
    pub timestamp: Timestamp<Chain>,
}

#[async_trait]
pub trait ChainStatusQuerier: ChainContext {
    async fn query_chain_status(&self) -> Result<ChainStatus<Self>, Self::Error>;
}
