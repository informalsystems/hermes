struct ConnectionError {
}

struct Connection {
}



struct ConnectionSideConfig {
    connection_id,
    chain_id, 
    client_id,
}

struct ConnectionConfig {
    src_config: ConnectionConfig,
    dest_config: ConnectionConfig,
}

impl Connection {
    fn new(src_chain: Chain, dest_chain: Chain, config: ConnectionConfig) -> Result<Connection, ConnectionError> {
        let connection = src_chain.query_connection(config.connection_id)?
        // Check the status of the established connection
        // * query connection on source chain
        // * query the destination chain
        // ** based on the status on the status from src and dest, we know what to do
        // * then we proceed with Handshake protocol
        return Ok(Connection{})
    }
}
