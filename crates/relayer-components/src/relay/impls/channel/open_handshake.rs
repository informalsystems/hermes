use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::channel::open_ack::CanRelayChannelOpenAck;
use crate::relay::traits::channel::open_confirm::CanRelayChannelOpenConfirm;
use crate::relay::traits::channel::open_handshake::ChannelOpenHandshakeRelayer;
use crate::relay::traits::channel::open_try::CanRelayChannelOpenTry;
use crate::std_prelude::*;

/**
   Relays a channel open handshake using a channel ID that has been
   initialized at the source chain, and the port IDs used.

   Specifically, the `ChanOpenTry`, `ChanOpenAck`, and `ChanOpenConfirm` steps of
   the handshake protocol are performed between both chains. Upon successful
   completion of the handshake protocol, a channel will have been established
   between both chains.

   This can be used for relaying of channels that are created by external
   users.
*/
pub struct RelayChannelOpenHandshake;

#[async_trait]
impl<Relay, SrcChain, DstChain> ChannelOpenHandshakeRelayer<Relay> for RelayChannelOpenHandshake
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanRelayChannelOpenTry
        + CanRelayChannelOpenAck
        + CanRelayChannelOpenConfirm,
    SrcChain: HasIbcChainTypes<DstChain>,
    DstChain: HasIbcChainTypes<SrcChain>,
{
    async fn relay_channel_open_handshake(
        relay: &Relay,
        src_channel_id: &SrcChain::ChannelId,
        src_port_id: &SrcChain::PortId,
        dst_port_id: &DstChain::PortId,
    ) -> Result<DstChain::ChannelId, Relay::Error> {
        let dst_channel_id = relay
            .relay_channel_open_try(dst_port_id, src_port_id, src_channel_id)
            .await?;

        relay
            .relay_channel_open_ack(src_port_id, src_channel_id, dst_port_id, &dst_channel_id)
            .await?;

        relay
            .relay_channel_open_confirm(dst_port_id, &dst_channel_id, src_port_id, src_channel_id)
            .await?;

        Ok(dst_channel_id)
    }
}
