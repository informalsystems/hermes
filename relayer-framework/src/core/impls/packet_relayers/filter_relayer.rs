use async_trait::async_trait;

use crate::core::traits::contexts::filter::FilterContext;
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FilterRelayer<InRelay> {
    pub in_relayer: InRelay,
}

impl<InRelay> FilterRelayer<InRelay> {
    pub fn new(in_relayer: InRelay) -> Self {
        Self { in_relayer }
    }
}

#[async_trait]
impl<Context, InRelay> PacketRelayer<Context> for FilterRelayer<InRelay>
where
    Context: FilterContext,
    InRelay: PacketRelayer<Context>,
{
    async fn relay_packet(
        &self,
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        if context.should_relay(packet) {
            self.in_relayer.relay_packet(context, packet).await?;
        }
        Ok(())
    }
}
