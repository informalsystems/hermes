use async_trait::async_trait;

use crate::chain::traits::components::message_sender::CanSendSingleMessage;
use crate::chain::traits::message_builders::channel::{
    CanBuildChannelHandshakeMessages, CanBuildChannelHandshakePayloads,
};
use crate::chain::traits::types::channel::HasInitChannelOptionsType;
use crate::chain::traits::types::ibc_events::channel::HasChannelOpenInitEvent;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::channel::open_init::ChannelInitializer;
use crate::std_prelude::*;

pub trait InjectMissingChannelInitEventError: HasRelayChains {
    fn missing_channel_init_event_error(&self) -> Self::Error;
}

/**
   A base implementation for [`ChannelInitializer`] which submits a
   `ChannelOpenInit` message to the source chain.

   This implements the `ChanOpenInit` step in the IBC channel handshake protocol.
*/

pub struct InitializeChannel;

#[async_trait]
impl<Relay, SrcChain, DstChain> ChannelInitializer<Relay> for InitializeChannel
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + InjectMissingChannelInitEventError,
    SrcChain: CanSendSingleMessage
        + HasInitChannelOptionsType<DstChain>
        + CanBuildChannelHandshakeMessages<DstChain>
        + HasChannelOpenInitEvent<DstChain>,
    DstChain: CanBuildChannelHandshakePayloads<SrcChain>,
    SrcChain::ChannelId: Clone,
{
    async fn init_channel(
        relay: &Relay,
        src_port_id: &SrcChain::PortId,
        dst_port_id: &DstChain::PortId,
        init_channel_options: &SrcChain::InitChannelOptions,
    ) -> Result<SrcChain::ChannelId, Relay::Error> {
        let src_chain = relay.src_chain();

        let src_message = src_chain
            .build_channel_open_init_message(src_port_id, dst_port_id, init_channel_options)
            .await
            .map_err(Relay::src_chain_error)?;

        let events = src_chain
            .send_message(src_message)
            .await
            .map_err(Relay::src_chain_error)?;

        let open_init_event = events
            .into_iter()
            .find_map(|event| SrcChain::try_extract_channel_open_init_event(event))
            .ok_or_else(|| relay.missing_channel_init_event_error())?;

        let src_channel_id = SrcChain::channel_open_init_event_channel_id(&open_init_event);

        Ok(src_channel_id.clone())
    }
}
