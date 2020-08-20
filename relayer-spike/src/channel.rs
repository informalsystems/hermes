use crate::chain::Chain;
use crate::types::{ChainId, ChannelId, ClientId, PortId};

pub struct ChannelError {
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
    config: ChannelConfig
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
    pub fn new(src_chain: Chain, dest_chain: Chain, config: ChannelConfig) -> Result<Channel, ChannelError> {
        // XXX: Perform the channel handshake
        return Ok(Channel{config})
    }
}
