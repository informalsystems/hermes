use core::marker::PhantomData;

use crate::core::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use crate::core::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::core::impls::packet_relayers::full_relay::FullRelayer;
use crate::core::impls::packet_relayers::retry::RetryRelayer;
use crate::core::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::core::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::traits::relay::OfaRelayContext;

pub fn full_packet_relayer<Relay>() -> impl PacketRelayer<OfaRelayContext<Relay>>
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    RetryRelayer::<
        FullRelayer<SkipReceivedPacketRelayer<BaseReceivePacketRelayer>, BaseAckPacketRelayer>,
    >::new(PhantomData)
}

pub fn receive_packet_relayer<Relay: OfaRelay>() -> impl ReceivePacketRelayer<OfaRelayContext<Relay>>
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    SkipReceivedPacketRelayer::<BaseReceivePacketRelayer>::new(PhantomData)
}

pub fn ack_packet_relayer<Relay>() -> impl AckPacketRelayer<OfaRelayContext<Relay>>
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    BaseAckPacketRelayer
}
