/// Structure used by the telemetry in order to define a UID
/// to track the SendPacket and WriteAcknowledgement for a given
/// chain, channel and port.

#[derive(Hash, PartialEq, Eq)]
pub struct PathIdentifier {
    chain_id: String,
    channel_id: String,
    port: String,
}

impl PathIdentifier {
    pub fn new(chain_id: String, channel_id: String, port: String) -> Self {
        Self {
            chain_id,
            channel_id,
            port,
        }
    }
}
