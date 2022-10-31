use std::fmt::{Display, Formatter, Result};

pub enum Message {
    SendPacket(u128),
    AckPacket(u128),
    TimeoutPacket(u128),
    UpdateClient(u128),
}

impl Display for Message {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::SendPacket(h) => write!(f, "SendPacket:{}", h),
            Self::AckPacket(h) => write!(f, "AckPacket:{}", h),
            Self::TimeoutPacket(h) => write!(f, "TimeoutPacket:{}", h),
            Self::UpdateClient(h) => write!(f, "UpdateClient:{}", h),
        }
    }
}
