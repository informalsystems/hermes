use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstChannelId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayChannelOpenTry: HasRelayChains {
    async fn relay_channel_open_try(
        &self,
        src_port_id: &SrcPortId<Self>,
        src_channel_id: &SrcChannelId<Self>,
    ) -> Result<DstChannelId<Self>, Self::Error>;
}

#[async_trait]
pub trait ChannelOpenTryRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_channel_open_try(
        relay: &Relay,
        src_port_id: &SrcPortId<Relay>,
        src_channel_id: &SrcChannelId<Relay>,
    ) -> Result<DstChannelId<Relay>, Relay::Error>;
}
