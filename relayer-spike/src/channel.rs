use crate::chain::Chain;
use crate::connection::Connection;
use crate::types::{ChainId, ChannelId, ClientId, PortId};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("Failed")]
    Failed(),
}

pub struct ChannelConfigSide {
    chain_id: ChainId,
    client_id: ClientId,
    channel_id: ChannelId,
    port_id: PortId,
}

pub struct ChannelConfig {
    src_config: ChannelConfigSide,
    dst_config: ChannelConfigSide,
}

pub struct Channel {
    config: ChannelConfig,
    pub src_chain: Box<dyn Chain>,
    pub dst_chain: Box<dyn Chain>,
}

impl ChannelConfig {
    pub fn default() -> ChannelConfig {
        return ChannelConfig {
            src_config: ChannelConfigSide { 
                port_id: "".to_string(), 
                channel_id: "".to_string(), 
                chain_id: 0, 
                client_id: "".to_string()
            },
            dst_config: ChannelConfigSide { 
                port_id: "".to_string(), 
                channel_id: "".to_string(), 
                chain_id: 0, 
                client_id: "".to_string(),
            },
        }
    }
}

impl Channel {
    pub fn new(connection: Connection, config: ChannelConfig) -> Result<Channel, ChannelError> {
        // XXX: Perform the channel handshake
        return Ok(Channel{
            config,
            src_chain: connection.src_chain,
            dst_chain: connection.dst_chain,
        })
    }
}
