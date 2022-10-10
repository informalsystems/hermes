use std::marker::PhantomData;

use crate::cosmos::base::all_for_one::relay::AfoCosmosRelayWrapper;
use ibc_relayer_framework::base::impls::packet_relayers::filter_relayer::FilterRelayer;
use ibc_relayer_framework::base::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::base::traits::contexts::filter::{HasPacketFilter, PacketFilter};
use ibc_relayer_framework::base::traits::packet_relayer::PacketRelayer;

pub fn full_packet_relayer<Relay, Filter>() -> PhantomData<impl PacketRelayer<Relay>>
where
    Relay: AfoCosmosRelayWrapper + HasPacketFilter<Filter = Filter>,
    Filter: PacketFilter<Relay>,
{
    PhantomData::<FilterRelayer<TopRelayer>>
}
