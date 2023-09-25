use async_trait::async_trait;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::components::chain_status_querier::CanQueryChainHeight;
use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::ibc_message_sender::{CanSendSingleIbcMessage, MainSink};
use crate::relay::traits::components::update_client_message_builder::CanSendUpdateClientMessage;
use crate::relay::traits::connection::open_ack::ConnectionOpenAckRelayer;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

/**
   A base implementation of [`ConnectionOpenAckRelayer`] that relays a new connection
   at the destination chain that is in `OPEN_TRY` state, and submits it as a
   `ConnectionOpenAck` message to the destination chain.

   This implements the `ConnOpenAck` step of the IBC connection handshake protocol.

   Note that this implementation does not check that the connections at the
   source and destination chain are really in the `OPEN_TRY` state. This will be
   implemented as a separate wrapper component. (TODO)
*/
pub struct RelayConnectionOpenAck;

#[async_trait]
impl<Relay, SrcChain, DstChain> ConnectionOpenAckRelayer<Relay> for RelayConnectionOpenAck
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanSendUpdateClientMessage<DestinationTarget>
        + CanSendSingleIbcMessage<MainSink, SourceTarget>,
    SrcChain: CanBuildConnectionHandshakeMessages<DstChain> + CanQueryClientState<DstChain>,
    DstChain: CanQueryChainHeight + CanBuildConnectionHandshakePayloads<SrcChain>,
    DstChain::ConnectionId: Clone,
{
    async fn relay_connection_open_ack(
        relay: &Relay,
        src_connection_id: &SrcChain::ConnectionId,
        dst_connection_id: &DstChain::ConnectionId,
    ) -> Result<(), Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let dst_client_id = relay.dst_client_id();

        let dst_proof_height = dst_chain
            .query_chain_height()
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_client_state = src_chain
            .query_client_state(relay.src_client_id())
            .await
            .map_err(Relay::src_chain_error)?;

        let open_ack_payload = dst_chain
            .build_connection_open_ack_payload(
                &dst_client_state,
                &dst_proof_height,
                dst_client_id,
                dst_connection_id,
            )
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_ack_message = src_chain
            .build_connection_open_ack_message(
                src_connection_id,
                dst_connection_id,
                open_ack_payload,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        relay.send_message(SourceTarget, open_ack_message).await?;

        Ok(())
    }
}
