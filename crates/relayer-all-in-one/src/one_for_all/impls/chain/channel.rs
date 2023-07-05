use async_trait::async_trait;

use ibc_relayer_components::chain::traits::message_builders::channel::CanBuildChannelHandshakeMessages;
use ibc_relayer_components::chain::traits::types::channel::HasInitChannelOptionsType;
use ibc_relayer_components::chain::traits::types::ibc_events::channel::HasChannelOpenInitEvent;

use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasInitChannelOptionsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type InitChannelOptions = Chain::InitChannelOptions;
}

impl<Chain, Counterparty> HasChannelOpenInitEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ChannelOpenInitEvent = Chain::ChannelOpenInitEvent;

    fn try_extract_channel_open_init_event(
        event: Chain::Event,
    ) -> Option<Chain::ChannelOpenInitEvent> {
        Chain::try_extract_channel_open_init_event(event)
    }

    fn channel_open_init_event_channel_id(
        event: &Chain::ChannelOpenInitEvent,
    ) -> &Chain::ChannelId {
        Chain::channel_open_init_event_channel_id(event)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildChannelHandshakeMessages<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_channel_open_init_message(
        &self,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_channel_open_init_message(init_channel_options)
            .await
    }
}
