use std::marker::PhantomData;

use crate::cosmos::all_for_one::relay::AfoCosmosRelayContext;
use ibc_relayer_framework::core::impls::packet_relayers::filter_relayer::FilterRelayer;
use ibc_relayer_framework::core::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::core::traits::contexts::filter::{HasPacketFilter, PacketFilter};
use ibc_relayer_framework::core::traits::packet_relayer::PacketRelayer;

pub fn full_packet_relayer<Relay, Filter>() -> impl PacketRelayer<Relay>
where
    Relay: AfoCosmosRelayContext + HasPacketFilter<Filter = Filter>,
    Filter: PacketFilter<Relay>,
{
    FilterRelayer::<TopRelayer>::new(PhantomData)
}
