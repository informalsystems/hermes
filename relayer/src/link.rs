use prost_types::Any;
use thiserror::Error;
use tracing::{error, info};

use ibc_proto::ibc::core::channel::v1::{
    MsgAcknowledgement as RawMsgAck, MsgRecvPacket as RawMsgRecvPacket,
    MsgTimeout as RawMsgTimeout, QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};

use ibc::{
    downcast,
    events::{IBCEvent, IBCEventType},
    ics04_channel::channel::{QueryPacketEventDataRequest, State},
    ics04_channel::events::{SendPacket, WriteAcknowledgement},
    ics04_channel::msgs::acknowledgement::MsgAcknowledgement,
    ics04_channel::msgs::recv_packet::MsgRecvPacket,
    ics04_channel::msgs::timeout::MsgTimeout,
    ics04_channel::packet::Packet,
    ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId},
    tx_msg::Msg,
    Height,
};

use crate::chain::handle::{ChainHandle, Subscription};
use crate::channel::{Channel, ChannelError};
use crate::config::ChainConfig;
use crate::connection::ConnectionError;
use crate::error::{Error, Kind};
use crate::foreign_client::build_update_client;
use ibc::ics04_channel::packet::PacketMsgType;

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
    pub channel: Channel,
}

fn send_update_client_and_msgs(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    msgs: &mut Vec<Any>,
    height: &Height,
    client_id: &ClientId,
) -> Result<(), Error> {
    if !msgs.is_empty() {
        let update_height = height.increment();
        let mut msgs_to_send =
            build_update_client(dst_chain.clone(), src_chain, client_id, update_height)?;
        msgs_to_send.append(msgs);
        info!("sending {:#?} messages", msgs_to_send.len());
        let res = dst_chain.send_msgs(msgs_to_send)?;
        info!("result {:#?}", res);
    }
    Ok(())
}

impl Link {
    pub fn new(channel: Channel) -> Link {
        Link { channel }
    }

    pub fn client_of_chain(&self, chain_id: ChainId) -> Option<&ClientId> {
        if chain_id == self.channel.config.a_config.chain_id().clone() {
            Some(&self.channel.config.a_config.client_id())
        } else if chain_id == self.channel.config.b_config.chain_id().clone() {
            Some(&self.channel.config.b_config.client_id())
        } else {
            None
        }
    }

    // Determines if the event received from the chain `from_chain` is relevant and
    // should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn must_process_event(&self, from_chain: Box<dyn ChainHandle>, event: &IBCEvent) -> bool {
        match event {
            IBCEvent::SendPacketChannel(send_packet_ev) => {
                self.channel.config.a_config.chain_id().clone() == from_chain.id()
                    && self.channel.config.a_config.channel_id().clone()
                        == send_packet_ev.envelope.packet_src_channel
                    && self.channel.config.a_config.port_id().clone()
                        == send_packet_ev.envelope.packet_src_port
                    || self.channel.config.b_config.chain_id().clone() == from_chain.id()
                        && self.channel.config.b_config.channel_id().clone()
                            == send_packet_ev.envelope.packet_src_channel
                        && self.channel.config.b_config.port_id().clone()
                            == send_packet_ev.envelope.packet_src_port
            }
            IBCEvent::WriteAcknowledgementChannel(write_ack_ev) => {
                self.channel.config.a_config.chain_id().clone() == from_chain.id()
                    && self.channel.config.a_config.channel_id().clone()
                        == write_ack_ev.envelope.packet_src_channel
                    && self.channel.config.a_config.port_id().clone()
                        == write_ack_ev.envelope.packet_src_port
                    || self.channel.config.b_config.chain_id().clone() == from_chain.id()
                        && self.channel.config.b_config.channel_id().clone()
                            == write_ack_ev.envelope.packet_src_channel
                        && self.channel.config.b_config.port_id().clone()
                            == write_ack_ev.envelope.packet_src_port
            }
            _ => false,
        }
    }

    fn relay_from_events(
        &self,
        src_chain: Box<dyn ChainHandle>,
        dst_chain: Box<dyn ChainHandle>,
        src_subscription: &Subscription,
    ) -> Result<(), LinkError> {
        let mut prev_height = Height::zero();
        let mut prev_msgs = vec![];

        let dst_height = dst_chain.query_latest_height()?;
        // Iterate through the IBC Events, build the message for each and collect all at same height.
        // Send a multi message transaction with these, prepending the client update
        for batch in src_subscription.try_iter().collect::<Vec<_>>().iter() {
            for event in batch.events.iter() {
                if !self.must_process_event(src_chain.clone(), event) {
                    continue;
                }
                let (packet_msg, _) =
                    handle_packet_event(dst_chain.clone(), dst_height, src_chain.clone(), event)?;

                // TODO add ICS height to IBC event
                let event_height = Height {
                    revision_height: u64::from(event.height()),
                    revision_number: ChainId::chain_version(src_chain.id().to_string().as_str()),
                };
                if prev_height == Height::zero() {
                    prev_height = event_height;
                }
                if event_height > prev_height {
                    send_update_client_and_msgs(
                        dst_chain.clone(),
                        src_chain.clone(),
                        &mut prev_msgs,
                        &prev_height,
                        self.client_of_chain(dst_chain.id()).unwrap(),
                    )?;
                    prev_height = event_height;
                }
                if let Some(msg) = packet_msg {
                    prev_msgs.append(&mut vec![msg]);
                }
            }
        }

        Ok(send_update_client_and_msgs(
            dst_chain.clone(),
            src_chain,
            &mut prev_msgs,
            &prev_height,
            self.client_of_chain(dst_chain.id()).unwrap(),
        )?)
    }

    pub fn run(&self) -> Result<(), LinkError> {
        info!("relaying packets for link {:#?}", self.channel.config);

        let a_chain = self.channel.connection().chain_a();
        let b_chain = self.channel.connection().chain_b();

        let a_subscription = &a_chain.subscribe(a_chain.id())?;
        let b_subscription = &b_chain.subscribe(b_chain.id())?;
        loop {
            self.relay_from_events(a_chain.clone(), b_chain.clone(), a_subscription)?;
            self.relay_from_events(b_chain.clone(), a_chain.clone(), b_subscription)?;
        }
    }
}

fn handle_packet_event(
    dst_chain: Box<dyn ChainHandle>,
    dst_height: Height,
    src_chain: Box<dyn ChainHandle>,
    event: &IBCEvent,
) -> Result<(Option<Any>, Option<Any>), Error> {
    match event {
        IBCEvent::SendPacketChannel(send_packet_ev) => {
            info!(
                "received from {:?} send packet event {:#?}",
                src_chain.id(),
                send_packet_ev.envelope
            );
            Ok(build_msg_from_send_packet_event(
                dst_chain,
                dst_height,
                src_chain,
                &send_packet_ev,
            )?)
        }
        IBCEvent::WriteAcknowledgementChannel(write_ack_ev) => {
            info!(
                "received from {:?} write ack event {:#?}",
                src_chain.id(),
                write_ack_ev.envelope
            );
            Ok((
                Some(build_packet_ack_msg_from_recv_event(
                    dst_chain,
                    src_chain,
                    &write_ack_ev,
                )?),
                None,
            ))
        }
        _ => Ok((None, None)),
    }
}

#[derive(Clone, Debug)]
pub struct PacketOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_client_id: ClientId,
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

fn build_recv_packet(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    packet: &Packet,
    height: Height,
) -> Result<Any, Error> {
    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let (_, proofs) = src_chain
        .build_packet_proofs(
            PacketMsgType::Recv,
            &packet.source_port,
            &packet.source_channel,
            u64::from(packet.sequence),
            height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg = MsgRecvPacket::new(packet.clone(), proofs, signer).map_err(|e| {
        Kind::RecvPacket(
            packet.source_channel.clone(),
            "error while building the recv packet".to_string(),
        )
        .context(e)
    })?;

    Ok(msg.to_any::<RawMsgRecvPacket>())
}

fn build_timeout_packet(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    packet: &Packet,
    height: Height,
) -> Result<Any, Error> {
    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let (_, proofs) = src_chain
        .build_packet_proofs(
            PacketMsgType::Timeout,
            &packet.source_port,
            &packet.source_channel,
            u64::from(packet.sequence),
            height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg = MsgTimeout::new(packet.clone(), packet.sequence, proofs, signer).map_err(|e| {
        Kind::TimeoutPacket(
            packet.source_channel.clone(),
            "error while building the timeout packet".to_string(),
        )
        .context(e)
    })?;

    Ok(msg.to_any::<RawMsgTimeout>())
}

fn build_msg_from_send_packet_event(
    dst_chain: Box<dyn ChainHandle>,
    dst_height: Height,
    src_chain: Box<dyn ChainHandle>,
    event: &SendPacket,
) -> Result<(Option<Any>, Option<Any>), Error> {
    let packet = Packet {
        sequence: event.envelope.clone().packet_sequence.into(),
        source_port: event.envelope.clone().packet_src_port,
        source_channel: event.envelope.clone().packet_src_channel,
        destination_port: event.envelope.clone().packet_dst_port,
        destination_channel: event.envelope.clone().packet_dst_channel,
        timeout_height: event.envelope.clone().packet_timeout_height,
        timeout_timestamp: event.envelope.clone().packet_timeout_stamp,
        data: event.clone().data,
    };

    // TODO - change event types to return ICS height
    let event_height = Height::new(
        ChainId::chain_version(src_chain.id().to_string().as_str()),
        u64::from(event.height),
    );

    if packet.timeout_height != Height::zero() && packet.timeout_height < dst_height {
        Ok((
            None,
            Some(build_timeout_packet(
                src_chain,
                dst_chain.clone(),
                &packet,
                dst_height,
            )?),
        ))
    // } else if packet.timeout_timestamp != 0 && packet.timeout_timestamp < dst_chain.query_time() {
    //     TODO - add query to get the current chain time
    } else {
        Ok((
            Some(build_recv_packet(
                dst_chain,
                src_chain,
                &packet,
                event_height,
            )?),
            None,
        ))
    }
}

/// From each sequence it builds either a MsgRecvPacket or a MsgTimeout message
/// MsgTimeout-s are sent to the source chain while MsgRecvPacket-s are sent to
/// the destination chain
fn build_packet_recv_msgs(
    dst_chain: Box<dyn ChainHandle>,
    dst_height: Height,
    src_chain: Box<dyn ChainHandle>,
    src_height: Height,
    src_channel_id: &ChannelId,
    src_port: &PortId,
    sequences: &[u64],
) -> Result<(Vec<Any>, Vec<Any>), Error> {
    if sequences.is_empty() {
        return Ok((vec![], vec![]));
    }
    // Set the height of the queries at height - 1
    // let query_height = src_height
    //     .decrement()
    //     .map_err(|e| Kind::InvalidHeight.context(e))?;

    let mut events = src_chain.query_txs(QueryPacketEventDataRequest {
        event_id: IBCEventType::SendPacket,
        port_id: src_port.to_string(),
        channel_id: src_channel_id.to_string(),
        sequences: Vec::from(sequences),
        height: src_height,
    })?;

    let mut packet_sequences = vec![];
    for event in events.iter() {
        let send_event = downcast!(event => IBCEvent::SendPacketChannel)
            .ok_or_else(|| Kind::Query.context("unexpected query tx response"))?;

        packet_sequences.append(&mut vec![send_event.envelope.packet_sequence]);
    }
    info!("received from query_txs {:?}", packet_sequences);

    let (mut recv_msgs, mut timeout_msgs) = (vec![], vec![]);
    for event in events.iter_mut() {
        event.set_height(src_height);
        let (recv, timeout) =
            handle_packet_event(dst_chain.clone(), dst_height, src_chain.clone(), event)?;
        if let Some(recv) = recv {
            recv_msgs.append(&mut vec![recv]);
        }
        if let Some(timeout) = timeout {
            timeout_msgs.append(&mut vec![timeout]);
        }
    }
    Ok((recv_msgs, timeout_msgs))
}

fn target_height_and_sequences_of_recv_packets(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &PacketOptions,
) -> Result<(Vec<u64>, Height), Error> {
    let src_channel = src_chain
        .query_channel(&opts.src_port_id, &opts.src_channel_id, Height::default())
        .map_err(|e| {
            Kind::RecvPacket(
                opts.src_channel_id.clone(),
                "source channel does not exist on source".into(),
            )
            .context(e)
        })?;

    let dst_channel_id = src_channel.counterparty().channel_id.ok_or_else(|| {
        Kind::RecvPacket(
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
            Kind::RecvPacket(
                dst_channel_id.clone(),
                "channel does not exist on destination chain".into(),
            )
            .context(e)
        })?;

    if dst_channel.state().clone() != State::Open {
        return Err(Kind::RecvPacket(
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
        return Ok((vec![], Height::zero()));
    }

    let mut src_sequences = vec![];
    for pc in packet_commitments.iter() {
        src_sequences.append(&mut vec![pc.sequence]);
    }
    info!(
        "packets that still have commitments on source {:?}",
        src_sequences
    );

    let request = QueryUnreceivedPacketsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_commitment_sequences: src_sequences,
    };

    let packets_to_send = dst_chain.query_unreceived_packets(request)?;

    info!(
        "packets to send out of the ones with commitments on source {:?}",
        packets_to_send
    );

    Ok((packets_to_send, query_height))
}

pub fn build_and_send_recv_packet_messages(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &PacketOptions,
) -> Result<Vec<String>, Error> {
    let (sequences, src_height) =
        target_height_and_sequences_of_recv_packets(dst_chain.clone(), src_chain.clone(), opts)?;
    if sequences.is_empty() {
        return Ok(vec!["No sent packets on source chain".to_string()]);
    }

    let dst_height = dst_chain.query_latest_height()?;

    let (mut recv_msgs, mut timeout_msgs) = build_packet_recv_msgs(
        dst_chain.clone(),
        dst_height,
        src_chain.clone(),
        src_height,
        &opts.src_channel_id,
        &opts.src_port_id,
        &sequences,
    )?;

    let mut result = vec![];
    if !recv_msgs.is_empty() {
        let mut dst_msgs = build_update_client(
            dst_chain.clone(),
            src_chain.clone(),
            &opts.dst_client_id.clone(),
            src_height.increment(),
        )?;
        dst_msgs.append(&mut recv_msgs);
        result.append(&mut dst_chain.send_msgs(dst_msgs)?);
    }

    if !timeout_msgs.is_empty() {
        let mut src_msgs = build_update_client(
            src_chain.clone(),
            dst_chain.clone(),
            &opts.dst_client_id.clone(),
            dst_height.increment(),
        )?;
        src_msgs.append(&mut timeout_msgs);
        result.append(&mut src_chain.clone().send_msgs(src_msgs)?);
    }
    Ok(result)
}

fn build_packet_ack_msg_from_recv_event(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    event: &WriteAcknowledgement,
) -> Result<Any, Error> {
    let packet = Packet {
        sequence: event.envelope.clone().packet_sequence.into(),
        source_port: event.envelope.clone().packet_src_port,
        source_channel: event.envelope.clone().packet_src_channel,
        destination_port: event.envelope.clone().packet_dst_port,
        destination_channel: event.envelope.clone().packet_dst_channel,
        timeout_height: event.envelope.clone().packet_timeout_height,
        timeout_timestamp: event.envelope.clone().packet_timeout_stamp,
        data: event.clone().data,
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

    let (_, proofs) = src_chain
        .build_packet_proofs(
            PacketMsgType::Ack,
            &event.envelope.packet_src_port,
            &event.envelope.packet_src_channel,
            event.envelope.packet_sequence,
            event_height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg = MsgAcknowledgement::new(packet.clone(), event.ack.clone(), proofs, signer).map_err(
        |e| {
            Kind::AckPacket(
                packet.source_channel,
                "error while building the ack packet".to_string(),
            )
            .context(e)
        },
    )?;

    Ok(msg.to_any::<RawMsgAck>())
}

fn build_packet_ack_msgs(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    src_channel_id: &ChannelId,
    src_port: &PortId,
    src_height: Height,
    sequences: &[u64],
) -> Result<Vec<Any>, Error> {
    if sequences.is_empty() {
        return Ok(vec![]);
    }
    // Set the height of the queries at height - 1
    let query_height = src_height
        .decrement()
        .map_err(|e| Kind::InvalidHeight.context(e))?;

    let mut events = src_chain.query_txs(QueryPacketEventDataRequest {
        event_id: IBCEventType::WriteAck,
        port_id: src_port.to_string(),
        channel_id: src_channel_id.to_string(),
        sequences: Vec::from(sequences),
        height: query_height,
    })?;

    let mut packet_sequences = vec![];
    for event in events.iter() {
        let write_ack_event = downcast!(event => IBCEvent::WriteAcknowledgementChannel)
            .ok_or_else(|| Kind::Query.context("unexpected query tx response"))?;

        packet_sequences.append(&mut vec![write_ack_event.envelope.packet_sequence]);
    }
    info!("received from query_txs {:?}", packet_sequences);

    let mut msgs = vec![];
    for event in events.iter_mut() {
        event.set_height(query_height);
        if let (Some(new_msg), _) = handle_packet_event(
            dst_chain.clone(),
            dst_chain.query_latest_height()?,
            src_chain.clone(),
            event,
        )? {
            msgs.append(&mut vec![new_msg]);
        }
    }
    Ok(msgs)
}

fn target_height_and_sequences_of_ack_packets(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &PacketOptions,
) -> Result<(Vec<u64>, Height), Error> {
    let src_channel = src_chain
        .query_channel(&opts.src_port_id, &opts.src_channel_id, Height::default())
        .map_err(|e| {
            Kind::AckPacket(
                opts.src_channel_id.clone(),
                "source channel does not exist on source".into(),
            )
            .context(e)
        })?;

    let dst_channel_id = src_channel.counterparty().channel_id.ok_or_else(|| {
        Kind::AckPacket(
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
            Kind::AckPacket(
                dst_channel_id.clone(),
                "channel does not exist on destination chain".into(),
            )
            .context(e)
        })?;

    if dst_channel.state().clone() != State::Open {
        return Err(Kind::AckPacket(
            dst_channel_id,
            "channel on destination not in open state".into(),
        )
        .into());
    }

    let pc_request = QueryPacketAcknowledgementsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: opts.src_channel_id.to_string(),
        pagination: None,
    };

    let (packet_acks, query_height) = src_chain.query_packet_acknowledgements(pc_request)?;

    if packet_acks.is_empty() {
        return Ok((vec![], Height::zero()));
    }

    let mut src_sequences = vec![];
    for pc in packet_acks.iter() {
        src_sequences.append(&mut vec![pc.sequence]);
    }
    info!(
        "packets that still have commitments on source {:?}",
        src_sequences
    );

    let request = QueryUnreceivedAcksRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_ack_sequences: src_sequences,
    };

    let packets_to_send = dst_chain.query_unreceived_acknowledgement(request)?;

    info!(
        "acks to send out of the ones with receipts on source {:?}",
        packets_to_send
    );

    Ok((packets_to_send, query_height))
}

pub fn build_and_send_ack_packet_messages(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &PacketOptions,
) -> Result<Vec<String>, Error> {
    let (sequences, height) =
        target_height_and_sequences_of_ack_packets(dst_chain.clone(), src_chain.clone(), opts)?;
    if sequences.is_empty() {
        return Ok(vec!["No sent packets on source chain".to_string()]);
    }

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst_client_id.clone(),
        height,
    )?;

    let mut packet_msgs = build_packet_ack_msgs(
        dst_chain.clone(),
        src_chain,
        &opts.src_channel_id,
        &opts.src_port_id,
        height,
        &sequences,
    )?;

    msgs.append(&mut packet_msgs);
    Ok(dst_chain.send_msgs(msgs)?)
}
