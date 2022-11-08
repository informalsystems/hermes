use core::marker::PhantomData;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::relay::impls::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullRelayer;
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::full::relay::impls::packet_relayers::retry::RetryRelayer;
use crate::base::relay::impls::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;

pub fn full_packet_relayer<Relay>() -> PhantomData<impl PacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaFullRelay,
    Relay::Preset: OfaRelayPreset<Relay>,
{
    PhantomData::<RetryRelayer<FullRelayer>>
}

pub fn receive_packet_relayer<Relay: OfaBaseRelay>(
) -> PhantomData<impl ReceivePacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaBaseRelay,
    Relay::Preset: OfaRelayPreset<Relay>,
{
    PhantomData::<SkipReceivedPacketRelayer<BaseReceivePacketRelayer>>
}

pub fn ack_packet_relayer<Relay>() -> PhantomData<impl AckPacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaBaseRelay,
    Relay::Preset: OfaRelayPreset<Relay>,
{
    PhantomData::<BaseAckPacketRelayer>
}
