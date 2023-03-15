use async_trait::async_trait;

use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait HasPacketLock: HasRelayTypes {
    type PacketLock<'a>: Send;

    async fn try_acquire_packet_lock<'a>(
        &'a self,
        packet: &'a Self::Packet,
    ) -> Option<Self::PacketLock<'a>>;
}
