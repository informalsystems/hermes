use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::base::types::height::Height;

#[derive(Debug, PartialEq)]
pub enum Event {
    RecvPacket(Height),
    WriteAcknowledgment(Height),
    SendPacket(SendPacketEvent),
}

#[derive(Debug)]
pub struct WriteAcknowledgementEvent(pub Height);

impl WriteAcknowledgementEvent {
    pub fn new(h: Height) -> Self {
        WriteAcknowledgementEvent(h)
    }
}

#[derive(Clone, Debug)]
pub struct SendPacketEvent {
    pub src_channel_id: String,
    pub src_port_id: String,
    pub dst_channel_id: String,
    pub dst_port_id: String,
    pub sequence: u128,
    pub timeout_height: Height,
    pub timeout_timestamp: MockTimestamp,
}

impl SendPacketEvent {
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
