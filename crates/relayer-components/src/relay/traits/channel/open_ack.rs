use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstChannelId, DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayChannelOpenAck: HasRelayChains {
    async fn relay_channel_open_ack(
        &self,
        src_port_id: &SrcPortId<Self>,
        src_channel_id: &SrcChannelId<Self>,
        dst_port_id: &DstPortId<Self>,
        dst_channel_id: &DstChannelId<Self>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait ChannelOpenAckRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_channel_open_ack(
        relay: &Relay,
        src_port_id: &SrcPortId<Relay>,
        src_channel_id: &SrcChannelId<Relay>,
        dst_port_id: &DstPortId<Relay>,
        dst_channel_id: &DstChannelId<Relay>,
    ) -> Result<(), Relay::Error>;
}
