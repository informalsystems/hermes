use async_trait::async_trait;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::components::chain_status_querier::CanQueryChainHeight;
use crate::chain::traits::message_builders::channel::{
    CanBuildChannelHandshakeMessages, CanBuildChannelHandshakePayloads,
};
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::channel::open_confirm::ChannelOpenConfirmRelayer;
use crate::relay::traits::components::ibc_message_sender::{CanSendSingleIbcMessage, MainSink};
use crate::relay::traits::target::DestinationTarget;
use crate::relay::types::aliases::{DstChannelId, DstPortId, SrcChannelId, SrcPortId};
use crate::std_prelude::*;

/**
   A base implementation of [`ChannelOpenConfirmRelayer`] that relays a new channel
   at the source chain that is in `OPEN` state, and submits it as a
   `ChannelOpenConfirm` message to the destination chain.

   This implements the `ChanOpenConfirm` step of the IBC channel handshake protocol.

   Note that this implementation does not check that the channel exists on
   the destination chain, that a channel exists on the source chain, and that the
   channel end at the source chain is really in the `OPEN` state. This will be implemented
   as a separate wrapper component. (TODO)
*/

pub struct RelayChannelOpenConfirm;

#[async_trait]
impl<Relay, SrcChain, DstChain> ChannelOpenConfirmRelayer<Relay> for RelayChannelOpenConfirm
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanSendSingleIbcMessage<MainSink, DestinationTarget>,
    SrcChain: CanQueryChainHeight + CanBuildChannelHandshakePayloads<DstChain>,
    DstChain: CanQueryClientState<SrcChain> + CanBuildChannelHandshakeMessages<SrcChain>,
{
    async fn relay_channel_open_confirm(
        relay: &Relay,
        dst_port_id: &DstPortId<Relay>,
        dst_channel_id: &DstChannelId<Relay>,
        src_port_id: &SrcPortId<Relay>,
        src_channel_id: &SrcChannelId<Relay>,
    ) -> Result<(), Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let src_proof_height = src_chain
            .query_chain_height()
            .await
            .map_err(Relay::src_chain_error)?;

        let src_client_state = dst_chain
            .query_client_state(relay.dst_client_id())
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_confirm_payload = src_chain
            .build_channel_open_confirm_payload(
                &src_client_state,
                &src_proof_height,
                src_port_id,
                src_channel_id,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        let open_confirm_message = dst_chain
            .build_channel_open_confirm_message(dst_port_id, dst_channel_id, open_confirm_payload)
            .await
            .map_err(Relay::dst_chain_error)?;

        relay
            .send_message(DestinationTarget, open_confirm_message)
            .await?;

        Ok(())
    }
}
