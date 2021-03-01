use send_packet::SendPacketResult;

pub mod send_packet;

#[derive(Clone, Debug, PartialEq)]
pub enum PacketType {
    Send,
    Recv,
    Ack,
    To,
    ToClose,
}

#[derive(Clone, Debug)]
pub enum PacketResult {
    Send(SendPacketResult),
}
