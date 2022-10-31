use crate::relayer_mock::base::types::height::Height;

#[derive(Clone)]
pub struct PacketKey {
    pub client_id: String,
    pub channel_id: String,
    pub port_id: String,
    pub sequence: u128,
    pub timeout_height: Height,
    pub timeout_timestamp: Height,
}

impl PacketKey {
    pub fn new(
        client_id: String,
        channel_id: String,
        port_id: String,
        sequence: u128,
        timeout_height: Height,
        timeout_timestamp: Height,
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
