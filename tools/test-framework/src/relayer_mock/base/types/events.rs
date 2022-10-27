#[derive(Debug)]
pub enum Event {
    RecvPacket(u128),
    WriteAcknowledgment(u128),
}

#[derive(Debug)]
pub struct WriteAcknowledgementEvent {}
