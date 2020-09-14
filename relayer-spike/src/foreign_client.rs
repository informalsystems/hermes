use crate::types::{ChainId, ClientId};
use crate::chain::Chain;

pub struct ForeignClientError {}

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
}

impl ForeignClient {
    pub fn new(
        _src_chain: Chain,
        _dst_chain: Chain,
        _config: ForeignClientConfig) -> Result<ForeignClient, ForeignClientError> {
        return Ok(ForeignClient{})
    }
}
