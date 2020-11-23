use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};
use thiserror::Error;

use crate::chain::{handle::ChainHandle, Chain};
use crate::connection::Connection;

#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("failed")]
    Failed,
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
}

impl ChannelConfig {
    pub fn new(src_config: ChannelConfigSide, dst_config: ChannelConfigSide) -> ChannelConfig {
        Self {
            src_config,
            dst_config,
        }
    }
}

impl Channel {
    pub fn new(
        src_chain: impl ChainHandle,
        dst_chain: impl ChainHandle,
        connection: Connection, // Semantic dependency
        config: ChannelConfig,
    ) -> Result<Channel, ChannelError> {
        // XXX: Perform the channel handshake
        Ok(Channel { config })
    }
}
