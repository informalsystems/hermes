use crate::types::{ChainId, ChannelId, ClientId, PortId, Datagram};
use crate::connection::{Connection, ConnectionConfig, ConnectionError};
use crate::channel::{Channel, ChannelConfig, ChannelError};
use crate::chain::Chain;

pub struct LinkError {}

enum Order {
    Ordered(),
    Unordered(),
}

struct ConfigSide {
    chain_id: ChainId,
    client_id: ClientId,
    channel_id: ChannelId,
    port_id: PortId,
}

pub struct LinkConfig {
    src_config: ConfigSide,
    dst_config: ConfigSide,
    order: Order,
}

impl LinkConfig {
    pub fn default() -> LinkConfig {
        return LinkConfig {
            src_config: ConfigSide { 
                port_id: "".to_string(), 
                channel_id: "".to_string(), 
                chain_id: 0, 
                client_id: "".to_string(),
            },
            dst_config: ConfigSide { 
                port_id: "".to_string(), 
                channel_id: "".to_string(), 
                chain_id: 0, 
                client_id: "".to_string(),
            },
            order: Order::Unordered(),
        }
    }
}

pub struct Link {
    pub src_chain: Chain,
    pub dst_chain: Chain,
}

impl From<ConnectionError> for LinkError {
    fn from(error: ConnectionError) -> Self {
        return LinkError {}
    }
}

impl From<ChannelError> for LinkError {
    fn from(error: ChannelError ) -> Self {
        return LinkError {}
    }
}

// TODO: Map between error types
impl Link {
    // We can probably pass in the connection and channel
    pub fn new(src: Chain, dst: Chain, config: LinkConfig) -> Result<Link, LinkError> {
        // we need to create to proper configs here
        //
        
        let connection = Connection::new(src, dst, ConnectionConfig::default())?;
        let channel = Channel::new(src, dst, ChannelConfig::default())?;
        // XXX: What about client, we need to establish a client

        return Ok(Link {
            src_chain: src,
            dst_chain: dst,
        })
    }

    // Assume subscription returns an iterator of all pending datagrams
    // pre-condition: connection and channel have been established
    // Iterator will error if channel or connection are broken
    pub fn pending_datagrams(&self) -> Vec<Datagram> {
        return vec![Datagram::NoOp()];
    }
}
