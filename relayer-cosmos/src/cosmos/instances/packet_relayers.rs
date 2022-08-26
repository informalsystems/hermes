use crate::cosmos::all_for_one::relay::AfoCosmosRelayContext;
use ibc_relayer_framework::core::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::core::traits::packet_relayer::PacketRelayer;

pub fn full_packet_relayer<Relay>(max_retry: usize) -> impl PacketRelayer<Relay>
where
    Relay: AfoCosmosRelayContext,
{
    TopRelayer::new(max_retry)
}
