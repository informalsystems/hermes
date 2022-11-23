use core::marker::PhantomData;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::impls::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use crate::base::relay::impls::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::full::relay::impls::packet_relayers::retry::RetryRelayer;

pub fn full_packet_relayer<Relay>() -> PhantomData<impl PacketRelayer<OfaRelayWrapper<Relay>>>
where
    Relay: OfaFullRelay,
    Relay::Preset: OfaRelayPreset<Relay>,
{
    PhantomData::<RetryRelayer<FullCycleRelayer>>
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
