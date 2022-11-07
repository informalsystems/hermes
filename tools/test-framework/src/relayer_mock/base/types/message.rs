use std::fmt::{Display, Formatter, Result};

use super::packet::PacketKey;

#[derive(Debug)]
pub enum Message {
    SendPacket(u128, u128, PacketKey),
    AckPacket(u128, PacketKey),
    TimeoutPacket(u128, PacketKey),
    UpdateClient(u128),
}

impl Display for Message {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::SendPacket(h, ch, p) => write!(f, "SendPacket:{}-{}: {}", h, ch, p),
            Self::AckPacket(h, p) => write!(f, "AckPacket:{}: {}", h, p),
            Self::TimeoutPacket(h, p) => write!(f, "TimeoutPacket:{}: {}", h, p),
            Self::UpdateClient(h) => write!(f, "UpdateClient:{}", h),
        }
    }
}
