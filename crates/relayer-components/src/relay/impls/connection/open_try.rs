use async_trait::async_trait;
use core::iter::Iterator;

use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::traits::queries::status::CanQueryChainHeight;
use crate::chain::traits::types::height::CanIncrementHeight;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::connection::HasConnectionOpenTryEvent;
use crate::chain::traits::wait::CanWaitChainReachHeight;
use crate::relay::impls::update_client::CanSendUpdateClientMessage;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_try::ConnectionOpenTryRelayer;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

pub trait InjectMissingConnectionTryEventError: HasRelayChains {
    fn missing_connection_try_event_error(
        &self,
        src_connection_id: &<Self::SrcChain as HasIbcChainTypes<Self::DstChain>>::ConnectionId,
    ) -> Self::Error;
}

/**
   A base implementation of [`ConnectionOpenTryRelayer`] that relays a new connection
   at the source chain that is in `OPEN_INIT` state, and submits it as a
   `ConnectionOpenTry` message to the destination chain.

   This implements the `ConnOpenTry` step of the IBC connection handshake protocol.

   Note that this implementation does not check that the connection at the source
   chain is really in the `OPEN_INIT` state. This will be implemented as a separate
   wrapper component. (TODO)
*/
pub struct RelayConnectionOpenTry;

#[async_trait]
impl<Relay, SrcChain, DstChain> ConnectionOpenTryRelayer<Relay> for RelayConnectionOpenTry
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanSendUpdateClientMessage<SourceTarget>
        + CanBuildUpdateClientMessage<DestinationTarget>
        + InjectMissingConnectionTryEventError,
    SrcChain:
        CanQueryChainHeight + CanIncrementHeight + CanBuildConnectionHandshakePayloads<DstChain>,
    DstChain: CanSendMessages
        + CanQueryChainHeight
        + CanWaitChainReachHeight
        + CanBuildConnectionHandshakeMessages<SrcChain>
        + HasConnectionOpenTryEvent<SrcChain>,
    DstChain::ConnectionId: Clone,
{
    async fn relay_connection_open_try(
        relay: &Relay,
        src_connection_id: &SrcChain::ConnectionId,
    ) -> Result<DstChain::ConnectionId, Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let src_client_id = relay.src_client_id();
        let dst_client_id = relay.dst_client_id();

        let dst_height = dst_chain
            .query_chain_height()
            .await
            .map_err(Relay::dst_chain_error)?;

        relay
            .send_update_client_messages(SourceTarget, &dst_height)
            .await?;

        let src_proof_height = src_chain
            .query_chain_height()
            .await
            .map_err(Relay::src_chain_error)?;

        let open_try_payload = src_chain
            .build_connection_open_try_payload(&src_proof_height, src_client_id, src_connection_id)
            .await
            .map_err(Relay::src_chain_error)?;

        let src_update_height =
            SrcChain::increment_height(&src_proof_height).map_err(Relay::src_chain_error)?;

        let dst_update_client_messages = relay
            .build_update_client_messages(DestinationTarget, &src_update_height)
            .await?;

        let open_try_message = dst_chain
            .build_connection_open_try_message(
                dst_client_id,
                src_client_id,
                src_connection_id,
                open_try_payload,
            )
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_messages = {
            let mut messages = dst_update_client_messages;
            messages.push(open_try_message);
            messages
        };

        dst_chain
            .wait_chain_reach_height(&dst_height)
            .await
            .map_err(Relay::dst_chain_error)?;

        let mut events = dst_chain
            .send_messages(dst_messages)
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_try_event = events
            .pop()
            .ok_or_else(|| relay.missing_connection_try_event_error(src_connection_id))?
            .into_iter()
            .find_map(|event| DstChain::try_extract_connection_open_try_event(event))
            .ok_or_else(|| relay.missing_connection_try_event_error(src_connection_id))?;

        let dst_connection_id = DstChain::connection_open_try_event_connection_id(&open_try_event);

        Ok(dst_connection_id.clone())
    }
}
