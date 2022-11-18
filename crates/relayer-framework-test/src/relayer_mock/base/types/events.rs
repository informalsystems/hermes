use crate::relayer_mock::base::types::height::Height;

#[derive(Debug)]
pub enum Event {
    RecvPacket(Height),
    WriteAcknowledgment(Height),
}

#[derive(Debug)]
pub struct WriteAcknowledgementEvent {}
