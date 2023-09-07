use async_trait::async_trait;
use core::iter::Iterator;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::components::chain_status_querier::CanQueryChainHeight;
use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::connection::HasConnectionOpenTryEvent;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::ibc_message_sender::{CanSendSingleIbcMessage, MainSink};
use crate::relay::traits::components::update_client_message_builder::CanSendUpdateClientMessage;
use crate::relay::traits::connection::open_try::ConnectionOpenTryRelayer;
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
        + CanSendSingleIbcMessage<MainSink, DestinationTarget>
        + InjectMissingConnectionTryEventError,
    SrcChain: CanQueryChainHeight + CanBuildConnectionHandshakePayloads<DstChain>,
    DstChain: CanQueryClientState<SrcChain>
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

        let src_proof_height = src_chain
            .query_chain_height()
            .await
            .map_err(Relay::src_chain_error)?;

        let src_client_state = dst_chain
            .query_client_state(relay.dst_client_id())
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_try_payload = src_chain
            .build_connection_open_try_payload(
                &src_client_state,
                &src_proof_height,
                src_client_id,
                src_connection_id,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        let open_try_message = dst_chain
            .build_connection_open_try_message(
                dst_client_id,
                src_client_id,
                src_connection_id,
                open_try_payload,
            )
            .await
            .map_err(Relay::dst_chain_error)?;

        let events = relay
            .send_message(DestinationTarget, open_try_message)
            .await?;

        let open_try_event = events
            .into_iter()
            .find_map(|event| DstChain::try_extract_connection_open_try_event(event))
            .ok_or_else(|| relay.missing_connection_try_event_error(src_connection_id))?;

        let dst_connection_id = DstChain::connection_open_try_event_connection_id(&open_try_event);

        Ok(dst_connection_id.clone())
    }
}
