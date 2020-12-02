#![allow(dead_code, unreachable_code, unused_imports, unused_variables)]

use thiserror::Error;
use tracing::{debug, error, info};

use ibc::{
    ics24_host::identifier::{ChannelId, ClientId, PortId},
    Height,
};

use crate::chain::handle::{ChainHandle, QueryPacketDataRequest};
use crate::chain::Chain;
use crate::channel::{Channel, ChannelConfigSide, ChannelError};
use crate::connection::ConnectionError;

use ibc::ics04_channel::channel::State;
use prost_types::Any;

use ibc_proto::ibc::core::channel::v1::{
    QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::foreign_client::build_update_client;
use ibc::events::IBCEvent;
use ibc::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc::ics04_channel::packet::Packet;
use ibc::ics23_commitment::commitment::CommitmentProof;

// TODO: move to config
const MAX_RETRIES: usize = 10_usize;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("Failed")]
    Failed,

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),

    #[error("ChainError:")]
    ChainError(#[from] Error),

    #[error("exhausted max number of retries:")]
    RetryError,
}

pub struct Link {
    channel: Channel,
}

impl Link {
    pub fn new(channel: Channel) -> Link {
        Link { channel }
    }

    pub fn run(
        &self,
        a_chain: impl ChainHandle,
        b_chain: impl ChainHandle,
    ) -> Result<(), LinkError> {
        info!("relaying packets");
        let a_subscription = &a_chain.subscribe(a_chain.id())?;
        let _b_subscription = &b_chain.subscribe(b_chain.id())?;
        loop {
            let mut prev_height = Height::zero();
            let mut prev_msgs = vec![];
            for a_batch in a_subscription.try_iter().collect::<Vec<_>>().iter() {
                for event in a_batch.events.iter() {
                    // TODO add height to IBC enum event
                    let (mut packet_msgs, event_height) =
                        handle_event(b_chain.clone(), a_chain.clone(), event)?;
                    if prev_height == Height::zero() {
                        prev_height = event_height;
                    }
                    if event_height > prev_height {
                        if prev_msgs.is_empty() {
                            continue;
                        }
                        let mut msgs_to_send = build_update_client(
                            b_chain.clone(),
                            a_chain.clone(),
                            self.channel.config.b_config.client_id(),
                            prev_height.increment(),
                        )?;
                        msgs_to_send.append(&mut prev_msgs);
                        debug!("sending {:#?} messages", msgs_to_send.len());
                        let res = b_chain.send_msgs(msgs_to_send)?;
                        debug!("result {:?}", res);
                        prev_height = event_height;
                    }
                    prev_msgs.append(&mut packet_msgs);
                }
            }
            if !prev_msgs.is_empty() {
                let mut msgs_to_send = build_update_client(
                    b_chain.clone(),
                    a_chain.clone(),
                    self.channel.config.b_config.client_id(),
                    prev_height.increment(),
                )?;
                msgs_to_send.append(&mut prev_msgs);
                debug!("sending {:#?} messages", msgs_to_send.len());
                let res = b_chain.send_msgs(msgs_to_send)?;
                debug!("result {:?}", res);
            }
            // let b_batch = b_subscription.recv().unwrap();
            // for event in b_batch.events.iter() {
            //     let msgs = handle_event(a_chain.clone(), b_chain.clone(), event, &self.channel.config.a_config)?;
            //     if !msgs.is_empty() {
            //         debug!("sending {:?} messages", msgs.len());
            //         a_chain.send_msgs(msgs)?;
            //     }
            // }
        }
        Ok(())
    }
}

fn handle_event(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    event: &IBCEvent,
) -> Result<(Vec<Any>, Height), Error> {
    debug!("received event {:#?}", event);
    match event {
        IBCEvent::SendPacketChannel(send_packet_ev) => {
            let (msg, height) = build_packet_recv_msg_from_send_event(
                dst_chain,
                src_chain,
                send_packet_ev,
            )
            .unwrap();
            Ok((vec![msg.to_any::<RawMsgRecvPacket>()], height))
        }
        _ => Ok((vec![], Height::zero())),
    }
}

pub enum PacketMsgType {
    PacketRecv,
}

use ibc::ics04_channel::events::SendPacket;
use ibc::ics24_host::identifier::ChainId;
use ibc::tx_msg::Msg;
use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as RawMsgRecvPacket;

fn build_packet_recv_msg_from_send_event(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    event: &SendPacket,
) -> Result<(MsgRecvPacket, Height), Error> {
    let packet = Packet {
        sequence: event.packet_sequence.into(),
        source_port: event.clone().packet_src_port,
        source_channel: event.clone().packet_src_channel,
        destination_port: event.clone().packet_dst_port,
        destination_channel: event.clone().packet_dst_channel,
        data: event.clone().packet_data,
        timeout_height: event.clone().packet_timeout_height,
        timeout_timestamp: event.clone().packet_timeout_stamp,
    };

    // TODO - change event types to return ICS height
    let event_height = Height::new(
        ChainId::chain_version(src_chain.id().to_string().as_str()),
        u64::from(event.height),
    );

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let res = src_chain.proven_packet_commitment(
        &event.packet_src_port,
        &event.packet_src_channel,
        event.packet_sequence,
        event_height,
    );
    let msg = MsgRecvPacket::new(
        packet,
        CommitmentProof::from(res.unwrap().1),
        event_height.increment(),
        signer,
    )
    .unwrap();

    debug!("MsgRecvPacket {:#?}", msg);
    Ok((msg, event_height))
}

fn build_packet_recv_msgs(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    src_channel_id: &ChannelId,
    src_port: &PortId,
    src_height: Height,
    sequences: &[u64],
) -> Result<Vec<Any>, Error> {
    // Set the height of the queries at height - 1
    let query_height = src_height
        .decrement()
        .map_err(|e| Kind::InvalidHeight.context(e))?;

    let mut msgs = vec![];
    let events = src_chain.query_txs(QueryPacketDataRequest {
        port_id: src_port.to_string(),
        channel_id: src_channel_id.to_string(),
        sequences: Vec::from(sequences),
    })?;

    let mut pk_sequences = vec![];
    for pc in events.iter() {
        pk_sequences.append(&mut vec![pc.sequence]);
    }
    debug!("received from query_txs {:?}", pk_sequences);

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    for packet in events.iter() {
        let res = src_chain.proven_packet_commitment(
            src_port,
            src_channel_id,
            u64::from(packet.sequence),
            query_height,
        );
        let msg = MsgRecvPacket::new(
            packet.clone(),
            CommitmentProof::from(res.unwrap().1),
            src_height,
            signer,
        )
        .unwrap();

        debug!("MsgRecvPacket {:#?}", msg);
        let mut new_msgs = vec![msg.to_any::<RawMsgRecvPacket>()];
        msgs.append(&mut new_msgs);
    }
    Ok(msgs)
}

#[derive(Clone, Debug)]
pub struct PacketOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_client_id: ClientId,
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

pub fn build_packet_recv(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &PacketOptions,
) -> Result<Vec<Any>, Error> {
    let src_channel = src_chain
        .query_channel(&opts.src_port_id, &opts.src_channel_id, Height::default())
        .map_err(|e| {
            Kind::PacketRecv(
                opts.src_channel_id.clone(),
                "source channel does not exist on source".into(),
            )
            .context(e)
        })?;

    let dst_channel_id = src_channel.counterparty().channel_id.ok_or_else(|| {
        Kind::PacketRecv(
            opts.src_channel_id.clone(),
            "missing counterparty channel id".into(),
        )
    })?;

    let dst_channel = dst_chain
        .query_channel(
            &src_channel.counterparty().port_id,
            &dst_channel_id,
            Height::default(),
        )
        .map_err(|e| {
            Kind::PacketRecv(
                dst_channel_id.clone(),
                "destination channel does not exist on destination chain".into(),
            )
            .context(e)
        })?;

    if dst_channel.state().clone() != State::Open {
        return Err(Kind::PacketRecv(
            dst_channel_id,
            "channel on destination not in open state".into(),
        )
        .into());
    }

    let pc_request = QueryPacketCommitmentsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: opts.src_channel_id.to_string(),
        pagination: None,
    };

    let (packet_commitments, query_height) = src_chain.query_packet_commitments(pc_request)?;

    if packet_commitments.is_empty() {
        return Ok(vec![]);
    }

    let mut src_sequences = vec![];
    for pc in packet_commitments.iter() {
        src_sequences.append(&mut vec![pc.sequence]);
    }
    debug!(
        "packets that still have commitments on source {:?}",
        src_sequences
    );

    let request = QueryUnreceivedPacketsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_commitment_sequences: src_sequences,
    };

    let packets_to_send = dst_chain.query_unreceived_packets(request)?;

    debug!(
        "packets_to_send out of the ones with commitments on source {:?}",
        packets_to_send
    );

    if packets_to_send.is_empty() {
        return Ok(vec![]);
    }

    let mut packet_msgs = build_packet_recv_msgs(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.src_channel_id,
        &opts.src_port_id,
        query_height,
        &packets_to_send,
    )?;

    if packet_msgs.is_empty() {
        Ok(vec![])
    } else {
        let mut msgs = build_update_client(
            dst_chain,
            src_chain,
            &opts.dst_client_id.clone(),
            query_height,
        )?;
        msgs.append(&mut packet_msgs);
        Ok(msgs)
    }
}

pub fn build_packet_recv_and_send(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &PacketOptions,
) -> Result<Vec<String>, Error> {
    let dst_msgs = build_packet_recv(dst_chain.clone(), src_chain, &opts)?;
    if dst_msgs.is_empty() {
        Ok(vec!["No sent packets on source chain".to_string()])
    } else {
        Ok(dst_chain.send_msgs(dst_msgs)?)
    }
}
