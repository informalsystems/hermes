use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::base::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::base::relay::traits::types::{HasRelayPacketFields, HasRelayTypes};
use crate::std_prelude::*;

pub struct SkipReceivedPacketRelayer<Relayer> {
    pub phantom: PhantomData<Relayer>,
}

#[async_trait]
impl<Relay, Relayer> ReceivePacketRelayer<Relay> for SkipReceivedPacketRelayer<Relayer>
where
    Relay: HasRelayTypes,
    Relayer: ReceivePacketRelayer<Relay>,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
    Relay::DstChain: CanQueryReceivedPacket<Relay::SrcChain>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>
    {
        let is_packet_received = relay
            .destination_chain()
            .query_is_packet_received(
                Relay::packet_dst_port(packet),
                Relay::packet_dst_channel_id(packet),
                Relay::packet_sequence(packet),
            )
            .await
            .map_err(Relay::dst_chain_error)?;

        if !is_packet_received {
            Relayer::relay_receive_packet(relay, source_height, packet).await
        } else {
            Ok(None)
        }
    }
}
