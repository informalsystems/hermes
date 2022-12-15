use alloc::string::String;
use std::fmt::Display;

use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::base::types::height::Height;

#[derive(Clone, Debug)]
pub struct PacketKey {
    pub client_id: String,
    pub channel_id: String,
    pub port_id: String,
    pub sequence: u128,
    pub timeout_height: Height,
    pub timeout_timestamp: MockTimestamp,
}

impl Display for PacketKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PacketKey{{ client_id: {}, channel_id: {}, port_id: {}, sequence: {}, timeout_height: {}, timeout_timestamp: {} }}", self.client_id, self.channel_id, self.port_id, self.sequence, self.timeout_height, self.timeout_timestamp)?;
        Ok(())
    }
}

impl PacketKey {
    pub fn new(
        client_id: String,
        channel_id: String,
        port_id: String,
        sequence: u128,
        timeout_height: Height,
        timeout_timestamp: MockTimestamp,
    ) -> Self {
        Self {
            client_id,
            channel_id,
            port_id,
            sequence,
            timeout_height,
            timeout_timestamp,
        }
    }
}
