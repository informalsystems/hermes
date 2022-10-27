#[derive(Debug)]
pub enum Event {
    PacketRecv(u128),
    WriteAcknowledgment(u128),
}

#[derive(Debug)]
pub struct WriteAcknowledgementEvent {}
