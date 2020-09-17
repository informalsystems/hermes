use crate::chain::Chain;
use crate::foreign_client::ForeignClient;
use crate::types::{ConnectionId, ChainId, ClientId};

#[derive(Debug)]
pub struct ConnectionError {
}

pub struct Connection {
    pub src_chain: Box<dyn Chain>,
    pub dst_chain: Box<dyn Chain>,
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
    pub fn new(foreign_client: ForeignClient, config: ConnectionConfig) -> Result<Connection, ConnectionError> {
        // Check the status of the established connection
        // * query connection on source chain
        // * query the destination chain
        // ** based on the status on the status from src and dest, we know what to do
        // * then we proceed with Handshake protocol
        return Ok(Connection{
            src_chain: foreign_client.src_chain,
            dst_chain: foreign_client.dst_chain,
        })
    }
}
