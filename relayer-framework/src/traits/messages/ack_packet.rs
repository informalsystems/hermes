use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::IbcEventContext;
use crate::traits::contexts::relay::RelayContext;
use crate::types::aliases::{Height, IbcMessage, WriteAcknowledgementEvent};

#[async_trait]
pub trait AckPacketMessageBuilder<Context: RelayContext>
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
{
    async fn build_ack_packet_message(
        &self,
        destination_height: &Height<Context::DstChain>,
        packet: &Context::Packet,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<IbcMessage<Context::SrcChain, Context::DstChain>, Context::Error>;
}
