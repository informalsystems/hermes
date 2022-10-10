use core::marker::PhantomData;

use crate::base::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use crate::base::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::impls::packet_relayers::full_relay::FullRelayer;
use crate::base::impls::packet_relayers::retry::RetryRelayer;
use crate::base::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::base::one_for_all::traits::relay::OfaRelay;
use crate::base::one_for_all::traits::relay::OfaRelayContext;
use crate::base::traits::packet_relayer::PacketRelayer;
use crate::base::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::traits::packet_relayers::receive_packet::ReceivePacketRelayer;

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
