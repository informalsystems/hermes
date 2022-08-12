use crate::all_for_one::traits::relay::AfoRelayContext;

use crate::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use crate::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::impls::packet_relayers::full_relay::FullRelayer;
use crate::impls::packet_relayers::retry::RetryRelayer;
use crate::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use crate::traits::packet_relayer::PacketRelayer;
use crate::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::traits::packet_relayers::receive_packet::ReceivePacketRelayer;

pub fn full_packet_relayer<Relay: AfoRelayContext>(max_retry: usize) -> impl PacketRelayer<Relay> {
    let relayer1 = FullRelayer {
        receive_relayer: receive_packet_relayer(),
        ack_relayer: ack_packet_relayer(),
    };

    RetryRelayer::new(max_retry, relayer1)
}

pub fn receive_packet_relayer<Relay: AfoRelayContext>() -> impl ReceivePacketRelayer<Relay> {
    SkipReceivedPacketRelayer::new(BaseReceivePacketRelayer)
}

pub fn ack_packet_relayer<Relay: AfoRelayContext>() -> impl AckPacketRelayer<Relay> {
    BaseAckPacketRelayer
}
