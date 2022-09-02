use async_trait::async_trait;
use core::marker::PhantomData;

use crate::core::traits::contexts::filter::PacketFilter;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FilterRelayer<Filter, InRelay> {
    pub in_relayer: InRelay,
    pub phantom: PhantomData<Filter>,
}

impl<Filter, InRelay> FilterRelayer<Filter, InRelay> {
    pub fn new(in_relayer: InRelay) -> Self {
        Self {
            in_relayer,
            phantom: PhantomData,
        }
    }
}

#[async_trait]
impl<Context, InRelay, Filter> PacketRelayer<Context> for FilterRelayer<Filter, InRelay>
where
    Context: RelayContext,
    Filter: PacketFilter<Context>,
    InRelay: PacketRelayer<Context>,
{
    async fn relay_packet(
        &self,
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        if Filter::should_relay(context, packet) {
            self.in_relayer.relay_packet(context, packet).await?;
        }
        Ok(())
    }
}
