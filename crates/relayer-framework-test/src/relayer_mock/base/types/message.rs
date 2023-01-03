use std::fmt::{Display, Formatter, Result};

use crate::relayer_mock::base::types::aliases::ChainState;
use crate::relayer_mock::base::types::aliases::ClientId;
use crate::relayer_mock::base::types::{height::Height, packet::PacketKey};

#[derive(Debug)]
pub enum Message {
    RecvPacket(Height, PacketKey),
    AckPacket(Height, PacketKey),
    TimeoutPacket(Height, PacketKey),
    UpdateClient(ClientId, Height, ChainState),
}

impl Display for Message {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::RecvPacket(h, p) => {
                write!(f, "RecvPacket:{}: {}", h, p)
            }
            Self::AckPacket(h, p) => write!(f, "AckPacket:{}: {}", h, p),
            Self::TimeoutPacket(h, p) => write!(f, "TimeoutPacket:{}: {}", h, p),
            Self::UpdateClient(from, h, s) => write!(f, "{}|UpdateClient:{}: {:?}", from, h, s),
        }
    }
}
