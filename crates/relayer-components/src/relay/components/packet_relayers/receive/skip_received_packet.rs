use core::marker::PhantomData;

use async_trait::async_trait;

use crate::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::relay::traits::components::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::relay::traits::packet::HasRelayPacketFields;
use crate::std_prelude::*;

pub struct SkipReceivedPacketRelayer<Relayer> {
    pub phantom: PhantomData<Relayer>,
}

#[async_trait]
impl<Relay, Relayer> ReceivePacketRelayer<Relay> for SkipReceivedPacketRelayer<Relayer>
where
    Relay: HasRelayPacketFields,
    Relayer: ReceivePacketRelayer<Relay>,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    Relay::DstChain: CanQueryReceivedPacket<Relay::SrcChain>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>
    {
        let is_packet_received = relay
            .dst_chain()
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
