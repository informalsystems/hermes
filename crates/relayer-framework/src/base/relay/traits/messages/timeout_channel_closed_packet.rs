use async_trait::async_trait;

use crate::base::chain::types::aliases::{Height, Message};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait TimeoutChannelClosedMessageBuilder<Relay: HasRelayTypes> {
    async fn build_timeout_channel_closed_message(
        relay: &Relay,
        height: Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}
