use async_trait::async_trait;

use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

/**
   Provides a packet lock mutex for packet relayers to coordinate and avoid
   relaying the same packet at the same time.

   Before a packet relayer starts relaying, it should try and acquire a
   [`PacketLock`](Self::PacketLock) from the relay context. The packet lock
   would act as a mutex guard and stays active for its lifetime duration.
   During this period, acquiring the packet lock for another packet would fail,
   and this would signal to other packet relayers to skip relaying the given
   packet.
*/
#[async_trait]
pub trait HasPacketLock: HasRelayPacket {
    /**
       The mutex guard for a locked packet. This should be kept alive while
       the packet relayer is relaying a packet.

       During the lifetime of an acquired packet lock, other calls to
       [`try_acquire_packet_lock`](Self::try_acquire_packet_lock) on the
       same packet should return `None`.
    */
    type PacketLock<'a>: Send;

    /**
       Try and acquire the lock for a given packet. Returns `Some` if the
       acquire is success, and `None` if the packet lock has already been
       acquired.

       When the method returns `None`, this signals that another packet relayer
       is already relaying a given packet, and the caller should abort any
       relaying operation for that packet.

       When the method returns `Some`, the caller should retain the
       [`PacketLock`](Self::PacketLock) value throughout the relaying operation
       for the given packet. This would cause other callers that try to lock
       the same packet to get `None` returned.
    */
    async fn try_acquire_packet_lock<'a>(
        &'a self,
        packet: &'a Self::Packet,
    ) -> Option<Self::PacketLock<'a>>;
}
