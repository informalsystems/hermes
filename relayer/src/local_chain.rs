use crate::config::LocalChainConfig;
use crate::error::Error;

pub struct LocalChain {
    pub config: LocalChainConfig,
}

impl LocalChain {
    pub fn from_config(config: LocalChainConfig) -> Result<Self, Error> {
        Ok(Self {
            config,
        })
    }

    // TODO -- add a generic interface to submit any type of IBC messages.
    /// Submits an IBC message for creating an IBC client on the chain. It is assumed that this is
    /// a client for a mock chain.
    pub fn create_client(&self, _client_id: &String) {
        unimplemented!()
    }
}