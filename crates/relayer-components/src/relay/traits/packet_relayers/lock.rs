use crate::relay::traits::types::HasRelayTypes;
use crate::runtime::traits::mutex::HasRuntimeWithMutex;


pub trait HasPacketWorkerLock: HasRelayTypes + HasRuntimeWithMutex {
    fn mutex_for_packet(&self, packet: &Self::Packet);
}
