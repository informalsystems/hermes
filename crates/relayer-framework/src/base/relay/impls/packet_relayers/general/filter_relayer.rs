use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::relay::traits::packet_filter::HasPacketFilter;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FilterRelayer<InRelay> {
    pub phantom: PhantomData<InRelay>,
}

#[async_trait]
impl<Context, InRelayer> PacketRelayer<Context> for FilterRelayer<InRelayer>
where
    Context: HasPacketFilter,
    InRelayer: PacketRelayer<Context>,
{
    async fn relay_packet(
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        if context.should_relay_packet(packet).await? {
            InRelayer::relay_packet(context, packet).await
        } else {
            Ok(())
        }
    }
}
