use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{Qualified, QueryUnreceivedPacketsRequest};
use ibc_relayer::link::packet_events::query_write_ack_events;
use ibc_relayer::path::PathIdentifiers;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
use ibc_relayer_types::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc_relayer_types::core::ics04_channel::msgs::timeout::MsgTimeout;
use ibc_relayer_types::core::ics04_channel::packet::{Packet, PacketMsgType, Sequence};
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::traits::message::{wrap_cosmos_message, CosmosMessage};
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;

pub struct CosmosReceivePacketPayload {
    pub height: Height,
    pub packet: Packet,
    pub proofs: Proofs,
}

pub struct CosmosAckPacketPayload {
    pub height: Height,
    pub packet: Packet,
    pub ack: Vec<u8>,
    pub proofs: Proofs,
}

pub struct CosmosTimeoutUnorderedPacketPayload {
    pub height: Height,
    pub packet: Packet,
    pub proofs: Proofs,
}

pub async fn build_receive_packet_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    packet: &Packet,
) -> Result<CosmosReceivePacketPayload, Error> {
    let height = *height;
    let packet = packet.clone();

    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let proofs = chain_handle
                .build_packet_proofs(
                    PacketMsgType::Recv,
                    &packet.source_port,
                    &packet.source_channel,
                    packet.sequence,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let packet = packet.clone();

            Ok(CosmosReceivePacketPayload {
                height,
                packet,
                proofs,
            })
        })
        .await
        .map_err(BaseError::join)?
}

pub fn build_receive_packet_message(
    payload: CosmosReceivePacketPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosIbcMessage::new(Some(payload.height), move |signer| {
        Ok(MsgRecvPacket::new(
            payload.packet.clone(),
            payload.proofs.clone(),
            signer.clone(),
        )
        .to_any())
    });

    Ok(wrap_cosmos_message(message))
}

pub async fn build_ack_packet_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    packet: &Packet,
    ack: &WriteAcknowledgement,
) -> Result<CosmosAckPacketPayload, Error> {
    let height = *height;
    let packet = packet.clone();
    let ack = ack.clone();

    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let proofs = chain_handle
                .build_packet_proofs(
                    PacketMsgType::Ack,
                    &packet.destination_port,
                    &packet.destination_channel,
                    packet.sequence,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let packet = packet.clone();
            let ack = ack.ack.clone();

            Ok(CosmosAckPacketPayload {
                height,
                packet,
                ack,
                proofs,
            })
        })
        .await
        .map_err(BaseError::join)?
}

pub fn build_ack_packet_message(
    payload: CosmosAckPacketPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosIbcMessage::new(Some(payload.height), move |signer| {
        Ok(MsgAcknowledgement::new(
            payload.packet.clone(),
            payload.ack.clone().into(),
            payload.proofs.clone(),
            signer.clone(),
        )
        .to_any())
    });

    Ok(wrap_cosmos_message(message))
}

pub async fn build_timeout_unordered_packet_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    packet: &Packet,
) -> Result<CosmosTimeoutUnorderedPacketPayload, Error> {
    let height = *height;
    let packet = packet.clone();

    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let proofs = chain_handle
                .build_packet_proofs(
                    PacketMsgType::TimeoutUnordered,
                    &packet.destination_port,
                    &packet.destination_channel,
                    packet.sequence,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let packet = packet.clone();

            Ok(CosmosTimeoutUnorderedPacketPayload {
                height,
                packet,
                proofs,
            })
        })
        .await
        .map_err(BaseError::join)?
}

pub fn build_timeout_unordered_packet_message(
    payload: CosmosTimeoutUnorderedPacketPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosIbcMessage::new(Some(payload.height), move |signer| {
        Ok(MsgTimeout::new(
            payload.packet.clone(),
            payload.packet.sequence,
            payload.proofs.clone(),
            signer.clone(),
        )
        .to_any())
    });

    Ok(wrap_cosmos_message(message))
}

pub async fn query_is_packet_received<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    port_id: &PortId,
    channel_id: &ChannelId,
    sequence: &Sequence,
) -> Result<bool, Error> {
    let chain_handle = chain.handle.clone();

    let port_id = port_id.clone();
    let channel_id = channel_id.clone();
    let sequence = *sequence;

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let unreceived_packet = chain_handle
                .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                    port_id: port_id.clone(),
                    channel_id: channel_id.clone(),
                    packet_commitment_sequences: vec![sequence],
                })
                .map_err(BaseError::relayer)?;

            let is_packet_received = unreceived_packet.is_empty();

            Ok(is_packet_received)
        })
        .await
        .map_err(BaseError::join)?
}

pub async fn query_write_acknowledgement_event<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    packet: &Packet,
) -> Result<Option<WriteAcknowledgement>, Error> {
    let chain_handle = chain.handle.clone();

    let packet = packet.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let status = chain_handle
                .query_application_status()
                .map_err(BaseError::relayer)?;

            let query_height = Qualified::Equal(status.height);

            let path_ident = PathIdentifiers {
                port_id: packet.destination_port.clone(),
                channel_id: packet.destination_channel.clone(),
                counterparty_port_id: packet.source_port.clone(),
                counterparty_channel_id: packet.source_channel.clone(),
            };

            let ibc_events = query_write_ack_events(
                &chain_handle,
                &path_ident,
                &[packet.sequence],
                query_height,
            )
            .map_err(BaseError::relayer)?;

            let write_ack = ibc_events.into_iter().find_map(|event_with_height| {
                let event = event_with_height.event;

                if let IbcEvent::WriteAcknowledgement(write_ack) = event {
                    Some(write_ack)
                } else {
                    None
                }
            });

            Ok(write_ack)
        })
        .await
        .map_err(BaseError::join)?
}
