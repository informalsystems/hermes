/// Structure used by the telemetry in order to define a UID
/// to track the SendPacket and WriteAcknowledgement and Timeouts for a given
/// chain, channel and port.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PathIdentifier {
    chain_id: String,
    channel_id: String,
    port_id: String,
}

impl PathIdentifier {
    pub fn new(chain_id: String, channel_id: String, port_id: String) -> Self {
        Self {
            chain_id,
            channel_id,
            port_id,
        }
    }
}
