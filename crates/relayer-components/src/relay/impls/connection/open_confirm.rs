use async_trait::async_trait;

use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::traits::queries::status::CanQueryChainHeight;
use crate::chain::traits::types::height::CanIncrementHeight;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_confirm::ConnectionOpenConfirmRelayer;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::DestinationTarget;
use crate::std_prelude::*;

/**
   A base implementation of [`ConnectionOpenConfirmRelayer`] that relays a new connection
   at the source chain that is in `OPEN` state, and submits it as a
   `ConnectionOpenConfirm` message to the destination chain.

   This implements the `ConnOpenConfirm` step of the IBC connection handshake protocol.

   Note that this implementation does not check that the connection at the source
   chain is really in the `OPEN` state, and that the connection at the destination chain
   is in the `OPEN_TRY` state. This will be implemented as a separate wrapper component. (TODO)
*/
pub struct RelayConnectionOpenConfirm;

#[async_trait]
impl<Relay, SrcChain, DstChain> ConnectionOpenConfirmRelayer<Relay> for RelayConnectionOpenConfirm
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanBuildUpdateClientMessage<DestinationTarget>,
    SrcChain:
        CanQueryChainHeight + CanIncrementHeight + CanBuildConnectionHandshakePayloads<DstChain>,
    DstChain: CanSendMessages + CanQueryChainHeight + CanBuildConnectionHandshakeMessages<SrcChain>,
    DstChain::ConnectionId: Clone,
{
    async fn relay_connection_open_confirm(
        relay: &Relay,
        src_connection_id: &SrcChain::ConnectionId,
        dst_connection_id: &DstChain::ConnectionId,
    ) -> Result<(), Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let src_client_id = relay.src_client_id();

        let src_proof_height = src_chain
            .query_chain_height()
            .await
            .map_err(Relay::src_chain_error)?;

        let open_confirm_payload = src_chain
            .build_connection_open_confirm_payload(
                &src_proof_height,
                src_client_id,
                src_connection_id,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        let src_update_height =
            SrcChain::increment_height(&src_proof_height).map_err(Relay::src_chain_error)?;

        let dst_update_client_messages = relay
            .build_update_client_messages(DestinationTarget, &src_update_height)
            .await?;

        let open_confirm_message = dst_chain
            .build_connection_open_confirm_message(dst_connection_id, open_confirm_payload)
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_messages = {
            let mut messages = dst_update_client_messages;
            messages.push(open_confirm_message);
            messages
        };

        dst_chain
            .send_messages(dst_messages)
            .await
            .map_err(Relay::dst_chain_error)?;

        Ok(())
    }
}
