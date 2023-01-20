use crate::relayer_mock::base::types::height::Height;

#[derive(Debug, PartialEq)]
pub enum Event {
    RecvPacket(Height),
    WriteAcknowledgment(Height),
}

#[derive(Debug)]
pub struct WriteAcknowledgementEvent(pub Height);

impl WriteAcknowledgementEvent {
    pub fn new(h: Height) -> Self {
        WriteAcknowledgementEvent(h)
    }
}
