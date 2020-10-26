use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use thiserror::Error;

use crate::chain::{handle::ChainHandle, Chain};
use crate::foreign_client::ForeignClient;

#[derive(Debug, Error)]
pub enum ConnectionError {
    #[error("Failed")]
    Failed(),
}

pub struct Connection {
    pub config: ConnectionConfig,
}

pub struct ConnectionSideConfig {
    pub connection_id: ConnectionId,
    pub chain_id: ChainId,
    pub client_id: ClientId,
}

pub struct ConnectionConfig {
    pub src_config: ConnectionSideConfig,
    pub dst_config: ConnectionSideConfig,
}

impl ConnectionConfig {
    pub fn new(_src: ConnectionSideConfig, _dst: ConnectionSideConfig) -> ConnectionConfig {
        todo!()
    }
}

impl Connection {
    pub fn new(
        _src_chain: &dyn ChainHandle,
        _dst_chain: &dyn ChainHandle,
        _foreign_client: &ForeignClient,
        config: ConnectionConfig,
    ) -> Result<Connection, ConnectionError> {
        // Check the status of the established connection
        // * query connection on source chain
        // * query the destination chain
        //   * based on the status on the status from src and dest, we know what to do
        // * then we proceed with Handshake protocol
        Ok(Connection { config })
    }
}
