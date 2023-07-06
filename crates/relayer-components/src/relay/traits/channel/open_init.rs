use async_trait::async_trait;

use crate::chain::traits::types::channel::HasInitChannelOptionsType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanInitChannel: HasRelayChains
where
    Self::SrcChain: HasInitChannelOptionsType<Self::DstChain>,
{
    async fn init_channel(
        &self,
        src_port_id: &SrcPortId<Self>,
        dst_port_id: &DstPortId<Self>,
        init_connection_options: &<Self::SrcChain as HasInitChannelOptionsType<
            Self::DstChain,
        >>::InitChannelOptions,
    ) -> Result<SrcChannelId<Self>, Self::Error>;
}

#[async_trait]
pub trait ChannelInitializer<Relay>
where
    Relay: HasRelayChains,
    Relay::SrcChain: HasInitChannelOptionsType<Relay::DstChain>,
{
    async fn init_channel(
        relay: &Relay,
        src_port_id: &SrcPortId<Relay>,
        dst_port_id: &DstPortId<Relay>,
        init_channel_options: &<Relay::SrcChain as HasInitChannelOptionsType<
        Relay::DstChain,
    >>::InitChannelOptions,
    ) -> Result<SrcChannelId<Relay>, Relay::Error>;
}
