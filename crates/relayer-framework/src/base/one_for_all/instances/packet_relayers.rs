use core::marker::PhantomData;

use crate::base::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::base::one_for_all::traits::relay::OfaRelay;
use crate::base::one_for_all::traits::relay::OfaRelayWrapper;
use crate::base::relay::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use crate::base::relay::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::relay::impls::packet_relayers::full_relay::FullRelayer;
use crate::base::relay::impls::packet_relayers::retry::RetryRelayer;
use crate::base::relay::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;

pub fn full_packet_relayer<Relay>() -> PhantomData<impl PacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    PhantomData::<RetryRelayer<FullRelayer>>
}

pub fn receive_packet_relayer<Relay: OfaRelay>(
) -> PhantomData<impl ReceivePacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    PhantomData::<SkipReceivedPacketRelayer<BaseReceivePacketRelayer>>
}

pub fn ack_packet_relayer<Relay>() -> PhantomData<impl AckPacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    PhantomData::<BaseAckPacketRelayer>
}
