use async_trait::async_trait;

use crate::chain::traits::message_builders::channel::{
    CanBuildChannelHandshakeMessages, CanBuildChannelHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::traits::queries::status::CanQueryChainHeight;
use crate::chain::traits::types::channel::HasChannelHandshakePayloads;
use crate::chain::traits::types::height::CanIncrementHeight;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::relay::impls::update_client::CanSendUpdateClientMessage;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::channel::open_ack::ChannelOpenAckRelayer;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::relay::types::aliases::{DstChannelId, DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

pub struct RelayChannelOpenAck;

#[async_trait]
impl<Relay, SrcChain, DstChain> ChannelOpenAckRelayer<Relay> for RelayChannelOpenAck
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanSendUpdateClientMessage<DestinationTarget>
        + CanBuildUpdateClientMessage<SourceTarget>,
    SrcChain:
        HasIbcChainTypes<DstChain> + CanSendMessages + CanBuildChannelHandshakeMessages<DstChain>,
    DstChain: HasIbcChainTypes<SrcChain>
        + CanQueryChainHeight
        + CanIncrementHeight
        + CanBuildChannelHandshakePayloads<SrcChain>
        + HasChannelHandshakePayloads<SrcChain>,
{
    async fn relay_channel_open_ack(
        relay: &Relay,
        src_port_id: &SrcPortId<Relay>,
        src_channel_id: &SrcChannelId<Relay>,
        dst_port_id: &DstPortId<Relay>,
        dst_channel_id: &DstChannelId<Relay>,
    ) -> Result<(), Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let dst_proof_height = dst_chain
            .query_chain_height()
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_ack_payload = dst_chain
            .build_channel_open_ack_payload(&dst_proof_height, dst_port_id, dst_channel_id)
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_update_height =
            DstChain::increment_height(&dst_proof_height).map_err(Relay::dst_chain_error)?;

        let src_update_client_messages = relay
            .build_update_client_messages(SourceTarget, &dst_update_height)
            .await?;

        let open_ack_message = src_chain
            .build_channel_open_ack_message(
                src_port_id,
                src_channel_id,
                dst_channel_id,
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
            .send_messages(src_messages)
            .await
            .map_err(Relay::src_chain_error)?;

        Ok(())
    }
}
