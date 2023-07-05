use async_trait::async_trait;

use crate::chain::traits::types::channel::HasInitChannelOptionsType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::SrcChannelId;
use crate::std_prelude::*;

#[async_trait]
pub trait CanInitChannel: HasRelayChains
where
    Self::SrcChain: HasInitChannelOptionsType<Self::DstChain>,
{
    async fn init_channel(
        &self,
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
        init_channel_options: &<Relay::SrcChain as HasInitChannelOptionsType<
        Relay::DstChain,
    >>::InitChannelOptions,
    ) -> Result<SrcChannelId<Relay>, Relay::Error>;
}
