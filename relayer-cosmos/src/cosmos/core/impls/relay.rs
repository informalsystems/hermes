use async_trait::async_trait;
use ibc::core::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
use ibc::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc::core::ics04_channel::msgs::timeout::MsgTimeout;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::PacketMsgType;
use ibc::core::ics04_channel::timeout::TimeoutHeight;
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::one_for_all::traits::chain::{OfaChain, OfaChainContext};
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelay;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::one_for_all::traits::telemetry::OfaTelemetryWrapper;

use crate::cosmos::core::error::Error;
use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::traits::relay::CosmosRelay;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::message::CosmosIbcMessage;
use crate::cosmos::core::types::relay::CosmosRelayContext;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;
use crate::cosmos::core::types::telemetry::CosmosTelemetry;

#[async_trait]
impl<Relay> OfaRelay for CosmosRelayContext<Relay>
where
    Relay: CosmosRelay,
{
    type Components = Relay::Components;

    type Error = Error;

    type Runtime = CosmosRuntimeContext;

    type SrcChain = CosmosChainContext<Relay::SrcChain>;

    type DstChain = CosmosChainContext<Relay::DstChain>;

    type Packet = Packet;

    type Telemetry = OfaTelemetryWrapper<CosmosTelemetry>;

    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::PortId {
        &packet.source_port
    }

    fn packet_src_channel_id(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::ChannelId {
        &packet.source_channel
    }

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::PortId {
        &packet.destination_port
    }

    fn packet_dst_channel_id(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::ChannelId {
        &packet.destination_channel
    }

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::Sequence {
        &packet.sequence
    }

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaChain>::Height> {
        match &packet.timeout_height {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(h) => Some(h),
        }
    }

    fn packet_timeout_timestamp(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::Timestamp {
        &packet.timeout_timestamp
    }

    fn runtime(&self) -> &OfaRuntimeContext<CosmosRuntimeContext> {
        &self.runtime
    }

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChain>::ClientId {
        &self.relay.dst_to_src_client().id
    }

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChain>::ClientId {
        &self.relay.src_to_dst_client().id
    }

    fn src_chain(&self) -> &OfaChainContext<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &OfaChainContext<Self::DstChain> {
        &self.dst_chain
    }

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChain>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChain>::Message>, Self::Error> {
        build_update_client_messages(self.relay.dst_to_src_client(), height)
    }

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChain>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChain>::Message>, Self::Error> {
        build_update_client_messages(self.relay.src_to_dst_client(), height)
    }

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaChain>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaChain>::Message, Self::Error> {
        let proofs = self
            .src_chain
            .chain
            .chain
            .chain_handle()
            .build_packet_proofs(
                PacketMsgType::Recv,
                &packet.source_port,
                &packet.source_channel,
                packet.sequence,
                *height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();

        let message = CosmosIbcMessage::new(Some(*height), move |signer| {
            Ok(MsgRecvPacket::new(packet.clone(), proofs.clone(), signer.clone()).to_any())
        });

        Ok(message)
    }

    fn telemetry(&self) -> &Self::Telemetry {
        &self.telemetry
    }

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChain>::Height,
        packet: &Self::Packet,
        ack: &<Self::DstChain as OfaChain>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChain>::Message, Self::Error> {
        let proofs = self
            .dst_chain
            .chain
            .chain
            .chain_handle()
            .build_packet_proofs(
                PacketMsgType::Ack,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                *destination_height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();
        let ack = ack.ack.clone();

        let message = CosmosIbcMessage::new(Some(*destination_height), move |signer| {
            Ok(MsgAcknowledgement::new(
                packet.clone(),
                ack.clone().into(),
                proofs.clone(),
                signer.clone(),
            )
            .to_any())
        });

        Ok(message)
    }

    /// Construct a timeout packet message to be sent back to the
    /// source chain over an unordered Cosmos channel.
    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChain>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::SrcChain as OfaChain>::Message, Self::Error> {
        let proofs = self
            .dst_chain
            .chain
            .chain
            .chain_handle()
            .build_packet_proofs(
                PacketMsgType::TimeoutUnordered,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                *destination_height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();

        let message = CosmosIbcMessage::new(Some(*destination_height), move |signer| {
            Ok(MsgTimeout::new(
                packet.clone(),
                packet.sequence,
                proofs.clone(),
                signer.clone(),
            )
            .to_any())
        });

        Ok(message)
    }
}

fn build_update_client_messages<DstChain, SrcChain>(
    foreign_client: &ForeignClient<DstChain, SrcChain>,
    height: &Height,
) -> Result<Vec<CosmosIbcMessage>, Error>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    let messages = foreign_client
        .build_update_client_with_trusted(height.increment(), None)
        .map_err(Error::foreign_client)?;

    let ibc_messages = messages
        .into_iter()
        .map(|update_message| {
            CosmosIbcMessage::new(Some(*height), move |signer| {
                let mut update_message = update_message.clone();
                update_message.signer = signer.clone();
                Ok(update_message.to_any())
            })
        })
        .collect();

    Ok(ibc_messages)
}
