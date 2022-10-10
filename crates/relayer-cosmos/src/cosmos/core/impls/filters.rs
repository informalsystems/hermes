use crate::cosmos::core::{
    traits::{filter::CosmosFilter, relay::CosmosRelay},
    types::relay::CosmosRelayContext,
};
use async_trait::async_trait;
use ibc_relayer::config::filter::PacketFilter as IbcChannelFilter;
use ibc_relayer_framework::{
    core::traits::contexts::{error::HasError, filter::PacketFilter},
    one_for_all::traits::relay::OfaRelayContext,
};
use ibc_relayer_types::core::ics04_channel::packet::Packet;

impl CosmosFilter for IbcChannelFilter {
    fn should_relay_packet(&self, packet: &Packet) -> bool {
        self.is_allowed(&packet.source_port, &packet.source_channel)
    }
}

#[derive(Clone)]
pub struct FilterWrapper<Filter: CosmosFilter> {
    pub inner_filter: Filter,
}

impl<Filter: CosmosFilter> FilterWrapper<Filter> {
    pub fn new(inner_filter: Filter) -> Self {
        Self { inner_filter }
    }

    pub fn inner_filter(&self) -> &Filter {
        &self.inner_filter
    }
}

#[async_trait]
impl<Relay, Filter> PacketFilter<OfaRelayContext<CosmosRelayContext<Relay, Filter>>>
    for FilterWrapper<Filter>
where
    Relay: CosmosRelay,
    Filter: CosmosFilter + Clone,
{
    async fn should_relay_packet(
        &self,
        packet: &Packet,
    ) -> Result<bool, <OfaRelayContext<CosmosRelayContext<Relay, Filter>> as HasError>::Error> {
        Ok(self.inner_filter().should_relay_packet(packet))
    }
}
