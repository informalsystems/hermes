use crate::types::{ChainId, ClientId};
use crate::chain::Chain;

#[derive(Debug)]
pub enum ForeignClientError {
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
    pub src_chain: Box<dyn Chain>,
    pub dst_chain: Box<dyn Chain>,
}

impl ForeignClient {
    pub fn new(
        src_chain: impl Chain + 'static,
        dst_chain: impl Chain + 'static,
        _config: ForeignClientConfig) -> Result<ForeignClient, ForeignClientError> {
        // TODO: Client Handshake
        return Ok(ForeignClient {
            src_chain: Box::new(src_chain),
            dst_chain: Box::new(dst_chain),
        })
    }

}
