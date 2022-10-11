use core::marker::PhantomData;

use crate::base::one_for_all::traits::components::relay::OfaBaseRelayComponents;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
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
    Relay: OfaBaseRelay,
    Relay::Components: OfaBaseRelayComponents<Relay>,
{
    PhantomData::<RetryRelayer<FullRelayer>>
}

pub fn receive_packet_relayer<Relay: OfaBaseRelay>(
) -> PhantomData<impl ReceivePacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaBaseRelay,
    Relay::Components: OfaBaseRelayComponents<Relay>,
{
    PhantomData::<SkipReceivedPacketRelayer<BaseReceivePacketRelayer>>
}

pub fn ack_packet_relayer<Relay>() -> PhantomData<impl AckPacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaBaseRelay,
    Relay::Components: OfaBaseRelayComponents<Relay>,
{
    PhantomData::<BaseAckPacketRelayer>
}
