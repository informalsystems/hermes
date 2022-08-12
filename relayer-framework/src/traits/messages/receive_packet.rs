use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait ReceivePacketMessageBuilder<Relay: RelayContext> {
    async fn build_receive_packet_message(
        &self,
        height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<IbcMessage<Relay::DstChain, Relay::SrcChain>, Relay::Error>;
}
