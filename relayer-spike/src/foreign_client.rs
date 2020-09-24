use crate::types::{ChainId, ClientId};
use crate::chain::Chain;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ForeignClientError {
    #[error("Fail")]
    Fail(),
}

pub struct ForeignClientConfig {
    client_id: ClientId,
    chain_id: ChainId,
}

impl ForeignClientConfig {
    pub fn default() -> ForeignClientConfig {
        return ForeignClientConfig {
            client_id: "".to_string(),
            chain_id: 0,
        }
    }
}

pub struct ForeignClient {
    config: ForeignClientConfig,
}

impl ForeignClient {
    pub fn new(
        src_chain: &dyn Chain,
        dst_chain: &dyn Chain,
        config: ForeignClientConfig) -> Result<ForeignClient, ForeignClientError> {
        // TODO: Client Handshake
        return Ok(ForeignClient {
            config,
        })
    }

    pub fn update(
        src_chain: impl Chain,
        dst_chain: impl Chain) -> Result<(), ForeignClientError> {
        // TODO
        return Ok(());
    }
}
