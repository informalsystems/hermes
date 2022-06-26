use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::CosmosRelayHandler;
use crate::impls::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::traits::packet_relayer::PacketRelayer;
use ibc::core::ics04_channel::packet::Packet;

pub async fn run_receive_packet_relayer<ChainA, ChainB>(
    context: &CosmosRelayHandler<ChainA, ChainB>,
    packet: Packet,
) -> Result<(), Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    ReceivePacketRelayer.relay_packet(context, packet).await?;

    Ok(())
}
