use async_trait::async_trait;

use crate::core::traits::contexts::filters::HasFilters;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::traits::filters::Filter;
use crate::core::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FilterRelayer<Filters : Filter, InRelay> {
    pub filters: Filters,
    pub in_relayer: InRelay,
}

impl<Filters, InRelay> FilterRelayer<Filters, InRelay> 
where Filters : Filter
{
    pub fn new(filters: Filters, in_relayer: InRelay) -> Self {
        Self {
            filters,
            in_relayer,
        }
    }
}

#[async_trait]
impl<Context, Filters, InRelay> PacketRelayer<Context> for FilterRelayer<Filters, InRelay>
where
    Context: RelayContext,
    InRelay: PacketRelayer<Context>,
    Filters: Filter,
{
    async fn relay_packet(
        &self,
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        if self.filters.allow() {
            self.in_relayer.relay_packet(context, packet).await?;
        }
        Ok(())
    }
}
