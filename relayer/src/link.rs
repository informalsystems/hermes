#![allow(dead_code, unreachable_code, unused_imports, unused_variables)]

use thiserror::Error;

use ibc::{
    ics24_host::identifier::{ChannelId, ClientId, PortId},
    Height,
};

use crate::chain::handle::{ChainHandle, QueryPacketDataRequest};
use crate::chain::Chain;
use crate::channel::{Channel, ChannelError, ChannelConfigSide};
use crate::connection::ConnectionError;

use ibc::ics04_channel::channel::State;
use prost_types::Any;

use ibc_proto::ibc::core::channel::v1::{
    Packet, QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::foreign_client::build_update_client;
use ibc::events::IBCEvent;
use ibc::ics04_channel::msgs::recv_packet::MsgRecvPacket;
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
        println!("relaying packets");
        let a_subscription = &a_chain.subscribe(a_chain.id())?;
        //let b_subscription = &b_chain.subscribe(b_chain.id())?;
        loop {
            let a_batch = a_subscription.recv().unwrap();
            //let b_batch = b_subscription.recv().unwrap();
            for event in a_batch.events.iter() {
                let msgs = handle_event(b_chain.clone(), a_chain.clone(), event, &self.channel.config.b_config)?;
                b_chain.send_tx(msgs)?;
            }
            // for event in b_batch.events.iter() {
            //     let msgs = handle_event(a_chain.clone(), b_chain.clone(), event, &self.channel.config.a_config)?;
            //     a_chain.send_tx(msgs)?;
            // }
        }
        Ok(())
    }
}

fn handle_event(dst_chain: impl ChainHandle, src_chain: impl ChainHandle, event: &IBCEvent, dst_config: &ChannelConfigSide
) -> Result<Vec<Any>, Error> {
    println!("Event from {:?} {:#?}", src_chain.id(), event);
    let mut msgs = vec![];
    if let IBCEvent::SendPacketChannel(send_packet_ev) = event {
        let event_height = Height::new(
            ChainId::chain_version(
                src_chain.id().to_string().as_str(),
            ),
            u64::from(send_packet_ev.height),
        );
        let query_height = event_height.increment();

        let mut packet_msgs = build_packet_recv_msgs(
            dst_chain.clone(),
            src_chain.clone(),
            &send_packet_ev.packet_src_channel,
            &send_packet_ev.packet_src_port,
            query_height,
            &[send_packet_ev.packet_sequence],
        )
            .unwrap();
        // TODO - collect all messages at same event height and only do the
        // client update once
        // Note - currently there is a problem with the transaction fee that is statically
        // fixed at 300000...it should be determined based on the Tx size
        if !packet_msgs.is_empty() {
            let mut client_msgs = build_update_client(
                dst_chain,
                src_chain,
                dst_config.client_id(),
                query_height,
            )?;
            msgs.append(&mut client_msgs);
            msgs.append(&mut packet_msgs);
            println!("sending {:?} messages", msgs.len());
        }
    }
    Ok(msgs)
}

pub enum PacketMsgType {
    PacketRecv,
}

use ibc::ics24_host::identifier::ChainId;
use ibc::tx_msg::Msg;
use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as RawMsgRecvPacket;

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

    let request = QueryUnreceivedPacketsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_commitment_sequences: src_sequences,
    };

    let packets_to_send = dst_chain.query_unreceived_packets(request)?;

    println!("packets_to_send {:?}", packets_to_send);

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
) -> Result<String, Error> {
    let dst_msgs = build_packet_recv(dst_chain.clone(), src_chain, &opts)?;
    if dst_msgs.is_empty() {
        Ok("No sent packets on source chain".to_string())
    } else {
        Ok(dst_chain.send_tx(dst_msgs)?)
    }
}
