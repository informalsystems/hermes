use crate::chain::Chain;
use crate::foreign_client::ForeignClient;
use crate::types::{ConnectionId, ChainId, ClientId};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ConnectionError {
    #[error("Failed")]
    Failed(),
}

pub struct Connection {
    config: ConnectionConfig,
}

struct ConnectionSideConfig {
    connection_id: ConnectionId,
    chain_id: ChainId,
    client_id: ClientId,
}

pub struct ConnectionConfig {
    src_config: ConnectionSideConfig,
    dst_config: ConnectionSideConfig,
}

impl ConnectionConfig {
    pub fn default() -> ConnectionConfig {
        return ConnectionConfig {
            src_config: ConnectionSideConfig { 
                connection_id: "".to_string(),
                 chain_id: 0,
                 client_id: "".to_string(),
            },
            dst_config: ConnectionSideConfig { 
                connection_id: "".to_string(),
                chain_id: 0,
                client_id: "".to_string(),
            },
        }
    }
}

impl Connection {
    pub fn new(
        _src_chain: &dyn Chain,
        _dst_chain: &dyn Chain,
        _foreign_client: &ForeignClient,
        config: ConnectionConfig) -> Result<Connection, ConnectionError> {
        // Check the status of the established connection
        // * query connection on source chain
        // * query the destination chain
        //   * based on the status on the status from src and dest, we know what to do
        // * then we proceed with Handshake protocol
        return Ok(Connection {
            config,
        })
    }
}
