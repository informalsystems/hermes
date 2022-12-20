use alloc::string::String;
use std::fmt::Display;

use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::base::types::height::Height;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PacketKey {
    pub src_channel_id: String,
    pub src_port_id: String,
    pub dst_channel_id: String,
    pub dst_port_id: String,
    pub sequence: u128,
    pub timeout_height: Height,
    pub timeout_timestamp: MockTimestamp,
}

impl Display for PacketKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PacketKey{{ src_channel_id: {}, dst_channel_id: {}, src_port_id: {}, dst_port_id: {}, sequence: {}, timeout_height: {}, timeout_timestamp: {} }}", self.src_channel_id, self.dst_channel_id, self.src_port_id, self.dst_port_id, self.sequence, self.timeout_height, self.timeout_timestamp)?;
        Ok(())
    }
}

impl PacketKey {
    pub fn new(
        src_channel_id: String,
        src_port_id: String,
        dst_channel_id: String,
        dst_port_id: String,
        sequence: u128,
        timeout_height: Height,
        timeout_timestamp: MockTimestamp,
    ) -> Self {
        Self {
            src_channel_id,
            src_port_id,
            dst_channel_id,
            dst_port_id,
            sequence,
            timeout_height,
            timeout_timestamp,
        }
    }
}
