use std::time::SystemTime;

pub struct PacketKey {
    pub client_id: String,
    pub channel_id: String,
    pub port_id: String,
    pub sequence: u128,
    pub height: u128,
    pub timeout: SystemTime,
}

impl PacketKey {
    pub fn new(
        client_id: String,
        channel_id: String,
        port_id: String,
        sequence: u128,
        height: u128,
        timeout: SystemTime,
    ) -> Self {
        Self {
            client_id,
            channel_id,
            port_id,
            sequence,
            height,
            timeout,
        }
    }
}
