use crate::cosmos::all_for_one::relay::AfoCosmosRelayContext;
use ibc_relayer_framework::core::impls::packet_relayers::filter_relayer::FilterRelayer;
use ibc_relayer_framework::core::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::core::traits::contexts::filter::PacketFilter;
use ibc_relayer_framework::core::traits::packet_relayer::PacketRelayer;

pub fn full_packet_relayer<Relay, Filter>(
    max_retry: usize,
    filter: Filter,
) -> impl PacketRelayer<Relay>
where
    Relay: AfoCosmosRelayContext,
    Filter: PacketFilter<Relay>,
{
    let inner_relayer = TopRelayer::new(max_retry);
    //let inner_relayer = full_packet_relayer::<Relay>(max_retry);
    FilterRelayer::new(filter, inner_relayer)
}
