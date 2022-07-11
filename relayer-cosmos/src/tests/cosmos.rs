use ibc::core::ics04_channel::packet::Packet;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_framework::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_framework::traits::packet_relayers::receive_packet::ReceivePacketRelayer;

use crate::cosmos::error::Error;
use crate::cosmos::handler::CosmosRelayHandler;

pub async fn run_receive_packet_relayer<ChainA, ChainB>(
    context: &CosmosRelayHandler<ChainA, ChainB>,
    height: Height,
    packet: Packet,
) -> Result<(), Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    SkipReceivedPacketRelayer::new(BaseReceivePacketRelayer)
        .relay_receive_packet(context, &height, &packet)
        .await?;

    Ok(())
}
