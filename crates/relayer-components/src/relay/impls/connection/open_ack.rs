use async_trait::async_trait;

use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::traits::queries::status::CanQueryChainHeight;
use crate::chain::traits::wait::CanWaitChainSurpassHeight;
use crate::relay::impls::update_client::CanSendUpdateClientMessage;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_ack::ConnectionOpenAckRelayer;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

pub struct RelayConnectionOpenAck;

#[async_trait]
impl<Relay, SrcChain, DstChain> ConnectionOpenAckRelayer<Relay> for RelayConnectionOpenAck
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanSendUpdateClientMessage<DestinationTarget>
        + CanBuildUpdateClientMessage<SourceTarget>,
    SrcChain: CanSendMessages
        + CanQueryChainHeight
        + CanWaitChainSurpassHeight
        + CanBuildConnectionHandshakeMessages<DstChain>,
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

        let src_height = src_chain
            .query_chain_height()
            .await
            .map_err(Relay::src_chain_error)?;

        relay
            .send_update_client_messages(DestinationTarget, &src_height)
            .await?;

        let dst_height = dst_chain
            .query_chain_height()
            .await
            .map_err(Relay::dst_chain_error)?;

        let src_update_client_messages = relay
            .build_update_client_messages(SourceTarget, &dst_height)
            .await?;

        let open_ack_payload = dst_chain
            .build_connection_open_ack_payload(&dst_height, dst_client_id, dst_connection_id)
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

        let src_messages = {
            let mut messages = src_update_client_messages;
            messages.push(open_ack_message);
            messages
        };

        src_chain
            .wait_chain_surpass_height(&src_height)
            .await
            .map_err(Relay::src_chain_error)?;

        src_chain
            .send_messages(src_messages)
            .await
            .map_err(Relay::src_chain_error)?;

        Ok(())
    }
}
