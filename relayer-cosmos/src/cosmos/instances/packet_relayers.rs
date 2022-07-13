use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_framework::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_framework::impls::packet_relayers::full_relay::FullRelayer;
use ibc_relayer_framework::impls::packet_relayers::retry::RetryRelayer;
use ibc_relayer_framework::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_framework::traits::packet_relayer::PacketRelayer;
use ibc_relayer_framework::traits::packet_relayers::ack_packet::AckPacketRelayer;
use ibc_relayer_framework::traits::packet_relayers::receive_packet::ReceivePacketRelayer;

use crate::cosmos::context::relay::CosmosRelayContext;

pub fn full_packet_relayer<ChainA, ChainB>(
    max_retry: usize,
) -> impl PacketRelayer<CosmosRelayContext<ChainA, ChainB>>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let relayer1 = FullRelayer {
        receive_relayer: receive_packet_relayer(),
        ack_relayer: ack_packet_relayer(),
    };

    let relayer2 = RetryRelayer {
        max_retry,
        in_relayer: relayer1,
    };

    relayer2
}

pub fn receive_packet_relayer<ChainA, ChainB>(
) -> impl ReceivePacketRelayer<CosmosRelayContext<ChainA, ChainB>>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    SkipReceivedPacketRelayer::new(BaseReceivePacketRelayer)
}

pub fn ack_packet_relayer<ChainA, ChainB>(
) -> impl AckPacketRelayer<CosmosRelayContext<ChainA, ChainB>>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    BaseAckPacketRelayer
}
