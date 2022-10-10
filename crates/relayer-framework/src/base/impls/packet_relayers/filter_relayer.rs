use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::traits::contexts::filter::{HasPacketFilter, PacketFilter};
use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::packet_relayer::PacketRelayer;
use crate::base::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FilterRelayer<InRelay> {
    pub phantom: PhantomData<InRelay>,
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
