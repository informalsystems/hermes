use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;
use ibc_relayer_framework::traits::packet_relayer::PacketRelayer;

use crate::cosmos::context::relay::CosmosRelayContext;

pub fn full_packet_relayer<ChainA, ChainB>(
    max_retry: usize,
) -> impl PacketRelayer<OfaRelayContext<CosmosRelayContext<ChainA, ChainB>>>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    TopRelayer::new(max_retry)
}
