use crate::all_for_one::traits::relay::AfoRelayContext;

use crate::core::impls::packet_relayers::top::{
    TopAckPacketRelayer, TopReceivePacketRelayer, TopRelayer,
};
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::core::traits::packet_relayers::receive_packet::ReceivePacketRelayer;

pub fn full_packet_relayer<Relay: AfoRelayContext>(max_retry: usize) -> impl PacketRelayer<Relay> {
    TopRelayer::new(max_retry)
}

pub fn receive_packet_relayer<Relay: AfoRelayContext>() -> impl ReceivePacketRelayer<Relay> {
    TopReceivePacketRelayer::new()
}

pub fn ack_packet_relayer<Relay: AfoRelayContext>() -> impl AckPacketRelayer<Relay> {
    TopAckPacketRelayer::new()
}
