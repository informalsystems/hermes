use async_trait::async_trait;

use crate::chain::traits::message_builders::channel::{
    CanBuildChannelHandshakeMessages, CanBuildChannelHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::traits::queries::status::CanQueryChainHeight;
use crate::chain::traits::types::height::CanIncrementHeight;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::channel::HasChannelOpenTryEvent;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::channel::open_try::ChannelOpenTryRelayer;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::DestinationTarget;
use crate::relay::types::aliases::{DstChannelId, DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

pub trait InjectMissingChannelTryEventError: HasRelayChains {
    fn missing_channel_try_event_error(
        &self,
        src_channel_id: &<Self::SrcChain as HasIbcChainTypes<Self::DstChain>>::ChannelId,
    ) -> Self::Error;
}

/**
   A base implementation of [`ChannelOpenTryRelayer`] that relays a new channel
   at the source chain that is in `OPEN_INIT` state, and submits it as a
   `ChannelOpenTry` message to the destination chain.

   This implements the `ChanOpenTry` step of the IBC channel handshake protocol.

   Note that this implementation does not check that the connection exists on
   the destination chain. It also doesn't check that the channel end at the
   source chain is really in the `OPEN_INIT` state. This will be implemented as
   a separate wrapper component. (TODO)
*/

pub struct RelayChannelOpenTry;

#[async_trait]
impl<Relay, SrcChain, DstChain> ChannelOpenTryRelayer<Relay> for RelayChannelOpenTry
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanBuildUpdateClientMessage<DestinationTarget>
        + InjectMissingChannelTryEventError,
    SrcChain: CanQueryChainHeight + CanIncrementHeight + CanBuildChannelHandshakePayloads<DstChain>,
    DstChain: CanSendMessages
        + CanBuildChannelHandshakeMessages<SrcChain>
        + HasChannelOpenTryEvent<SrcChain>,
    DstChain::ChannelId: Clone,
{
    async fn relay_channel_open_try(
        relay: &Relay,
        dst_port: &DstPortId<Relay>,
        src_port_id: &SrcPortId<Relay>,
        src_channel_id: &SrcChannelId<Relay>,
    ) -> Result<DstChannelId<Relay>, Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let src_proof_height = src_chain
            .query_chain_height()
            .await
            .map_err(Relay::src_chain_error)?;

        let open_try_payload = src_chain
            .build_channel_open_try_payload(&src_proof_height, src_port_id, src_channel_id)
            .await
            .map_err(Relay::src_chain_error)?;

        let src_update_height =
            SrcChain::increment_height(&src_proof_height).map_err(Relay::src_chain_error)?;

        let dst_update_client_messages = relay
            .build_update_client_messages(DestinationTarget, &src_update_height)
            .await?;

        let open_try_message = dst_chain
            .build_channel_open_try_message(dst_port, src_port_id, src_channel_id, open_try_payload)
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_messages = {
            let mut messages = dst_update_client_messages;
            messages.push(open_try_message);
            messages
        };

        let mut events = dst_chain
            .send_messages(dst_messages)
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_try_event = events
            .pop()
            .ok_or_else(|| relay.missing_channel_try_event_error(src_channel_id))?
            .into_iter()
            .find_map(|event| DstChain::try_extract_channel_open_try_event(event))
            .ok_or_else(|| relay.missing_channel_try_event_error(src_channel_id))?;

        let dst_channel_id = DstChain::channel_open_try_event_channel_id(&open_try_event);

        Ok(dst_channel_id.clone())
    }
}
