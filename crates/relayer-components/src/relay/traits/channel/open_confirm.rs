use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstChannelId, DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayChannelOpenConfirm: HasRelayChains {
    async fn relay_channel_open_confirm(
        &self,
        dst_port: &DstPortId<Self>,
        dst_channel_id: &DstChannelId<Self>,
        src_port_id: &SrcPortId<Self>,
        src_channel_id: &SrcChannelId<Self>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait ChannelOpenConfirmRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_channel_open_confirm(
        relay: &Relay,
        dst_port: &DstPortId<Relay>,
        dst_channel_id: &DstChannelId<Relay>,
        src_port_id: &SrcPortId<Relay>,
        src_channel_id: &SrcChannelId<Relay>,
    ) -> Result<(), Relay::Error>;
}
