use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstChannelId, DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayChannelOpenHandshake: HasRelayChains {
    async fn relay_channel_open_handshake(
        &self,
        src_channel_id: &SrcChannelId<Self>,
        src_port_id: &SrcPortId<Self>,
        dst_port_id: &DstPortId<Self>,
    ) -> Result<DstChannelId<Self>, Self::Error>;
}

#[async_trait]
pub trait ChannelOpenHandshakeRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_channel_open_handshake(
        relay: &Relay,
        src_channel_id: &SrcChannelId<Relay>,
        src_port_id: &SrcPortId<Relay>,
        dst_port_id: &DstPortId<Relay>,
    ) -> Result<DstChannelId<Relay>, Relay::Error>;
}
