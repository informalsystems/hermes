use async_trait::async_trait;

use ibc_relayer_components::relay::impls::channel::open_init::{
    InitializeChannel, InjectMissingChannelInitEventError,
};
use ibc_relayer_components::relay::traits::channel::open_init::{
    CanInitChannel, ChannelInitializer,
};

use crate::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use crate::one_for_all::{traits::relay::OfaRelay, types::relay::OfaRelayWrapper};
use crate::std_prelude::*;

impl<Relay> InjectMissingChannelInitEventError for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn missing_channel_init_event_error(&self) -> Relay::Error {
        self.relay.missing_channel_init_event_error()
    }
}

#[async_trait]
impl<Relay> CanInitChannel for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn init_channel(
        &self,
        init_channel_options: &<Relay::SrcChain as OfaIbcChain<Relay::DstChain>>::InitChannelOptions,
    ) -> Result<<Relay::SrcChain as OfaChain>::ChannelId, Self::Error> {
        InitializeChannel::init_channel(self, init_channel_options).await
    }
}
