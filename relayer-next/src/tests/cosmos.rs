use ibc::core::ics04_channel::packet::Packet;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::CosmosRelayHandler;
use crate::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::traits::messages::receive_packet::ReceivePacketRelayer;

pub async fn run_receive_packet_relayer<ChainA, ChainB>(
    context: &CosmosRelayHandler<ChainA, ChainB>,
    height: Height,
    packet: Packet,
) -> Result<(), Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    BaseReceivePacketRelayer
        .relay_receive_packet(context, &height, &packet)
        .await?;

    Ok(())
}
