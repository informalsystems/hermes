use async_trait::async_trait;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::base::traits::contexts::filter::HasPacketFilter;
use ibc_relayer_types::core::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
use ibc_relayer_types::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc_relayer_types::core::ics04_channel::msgs::timeout::MsgTimeout;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::PacketMsgType;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use ibc_relayer_framework::base::one_for_all::traits::chain::{OfaChainTypes, OfaChainWrapper};
use ibc_relayer_framework::base::one_for_all::traits::relay::OfaRelay;

use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::cosmos::base::error::Error;
use crate::cosmos::base::impls::filters::FilterWrapper;

use crate::cosmos::base::traits::chain::CosmosChain;
use crate::cosmos::base::traits::filter::CosmosFilter;
use crate::cosmos::base::traits::relay::CosmosRelay;
use crate::cosmos::base::types::chain::CosmosChainWrapper;
use crate::cosmos::base::types::message::CosmosIbcMessage;
use crate::cosmos::base::types::relay::CosmosRelayWrapper;
use crate::cosmos::base::types::runtime::CosmosRuntimeContext;

#[async_trait]
impl<Relay, Filter> OfaRelay for CosmosRelayWrapper<Relay, Filter>
where
    Relay: CosmosRelay,
    Filter: CosmosFilter + Clone,
{
    type Components = Relay::Components;

    type Error = Error;

    type Runtime = CosmosRuntimeContext;

    type SrcChain = CosmosChainWrapper<Relay::SrcChain>;

    type DstChain = CosmosChainWrapper<Relay::DstChain>;

    type Packet = Packet;

    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaChainTypes>::PortId {
        &packet.source_port
    }

    fn packet_src_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::SrcChain as OfaChainTypes>::ChannelId {
        &packet.source_channel
    }

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaChainTypes>::PortId {
        &packet.destination_port
    }

    fn packet_dst_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaChainTypes>::ChannelId {
        &packet.destination_channel
    }

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaChainTypes>::Sequence {
        &packet.sequence
    }

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaChainTypes>::Height> {
        match &packet.timeout_height {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(h) => Some(h),
        }
    }

    fn packet_timeout_timestamp(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaChainTypes>::Timestamp {
        &packet.timeout_timestamp
    }

    fn runtime(&self) -> &OfaRuntimeContext<CosmosRuntimeContext> {
        &self.runtime
    }

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChainTypes>::ClientId {
        &self.relay.dst_to_src_client().id
    }

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChainTypes>::ClientId {
        &self.relay.src_to_dst_client().id
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        &self.dst_chain
    }

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChainTypes>::Message>, Self::Error> {
        build_update_client_messages(self.relay.dst_to_src_client(), height)
    }

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChainTypes>::Message>, Self::Error> {
        build_update_client_messages(self.relay.src_to_dst_client(), height)
    }

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaChainTypes>::Message, Self::Error> {
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

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
        ack: &<Self::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
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

    /// Construct a timeout packet message to be sent between Cosmos chains
    /// over an unordered Cosmos channel.
    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
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

impl<Relay, Filter> HasPacketFilter for CosmosRelayWrapper<Relay, Filter>
where
    Relay: CosmosRelay,
    Filter: CosmosFilter + Clone,
{
    type Filter = FilterWrapper<Filter>;

    fn filter(&self) -> &Self::Filter {
        &self.filter
    }
}
