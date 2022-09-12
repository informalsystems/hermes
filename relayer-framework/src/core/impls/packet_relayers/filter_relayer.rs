use core::marker::PhantomData;

use async_trait::async_trait;

use crate::core::traits::contexts::filter::{HasPacketFilter, PacketFilter};
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FilterRelayer<InRelay> {
    pub phantom: PhantomData<InRelay>,
}

impl<InRelay> FilterRelayer<InRelay> {
    pub fn new(phantom: PhantomData<InRelay>) -> Self {
        Self { phantom }
    }
}

#[async_trait]
impl<Context, InRelay, Filter> PacketRelayer<Context> for FilterRelayer<InRelay>
where
    Context: RelayContext + HasPacketFilter<Filter = Filter>,
    Filter: PacketFilter<Context>,
    InRelay: PacketRelayer<Context>,
{
    async fn relay_packet(
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        if context.filter().should_relay_packet(packet).await? {
            InRelay::relay_packet(context, packet).await?;
        }
        Ok(())
    }
}
