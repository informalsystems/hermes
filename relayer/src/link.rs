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
use crate::foreign_client::{build_update_client, ForeignClient};
use crate::relay::MAX_ITER;
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics24_host::identifier::ConnectionId;

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
    src_chain: Box<dyn ChainHandle>,
    dst_chain: Box<dyn ChainHandle>,
    subscription: Subscription,
    channel: Channel,
    all_events: Vec<IBCEvent>,
    src_height: Height,
    dst_height: Height,
    dst_msgs_input_events: Vec<IBCEvent>,
    src_msgs_input_envens: Vec<IBCEvent>,
    packet_msgs: Vec<Any>,
    timeout_msgs: Vec<Any>,
}

impl Link {
    fn new(
        src_chain: Box<dyn ChainHandle>,
        dst_chain: Box<dyn ChainHandle>,
        channel: Channel,
    ) -> Result<Self, LinkError> {
        Ok(Link {
            src_chain: src_chain.clone(),
            dst_chain: dst_chain.clone(),
            subscription: src_chain.subscribe()?,
            channel,
            all_events: vec![],
            src_height: Height::zero(),
            dst_height: Height::zero(),
            dst_msgs_input_events: vec![],
            src_msgs_input_envens: vec![],
            packet_msgs: vec![],
            timeout_msgs: vec![],
        })
    }

    pub fn src_chain(&self) -> Box<dyn ChainHandle> {
        self.src_chain.clone()
    }

    pub fn dst_chain(&self) -> Box<dyn ChainHandle> {
        self.dst_chain.clone()
    }

    pub fn src_client_id(&self) -> &ClientId {
        &self.channel.src_client_id()
    }

    pub fn dst_client_id(&self) -> &ClientId {
        &self.channel.dst_client_id()
    }

    pub fn src_connection_id(&self) -> &ConnectionId {
        &self.channel.src_connection_id()
    }

    pub fn dst_connection_id(&self) -> &ConnectionId {
        &self.channel.dst_connection_id()
    }

    pub fn src_port_id(&self) -> &PortId {
        &self.channel.src_port_id()
    }

    pub fn dst_port_id(&self) -> &PortId {
        &self.channel.dst_port_id()
    }

    pub fn src_channel_id(&self) -> &ChannelId {
        &self.channel.src_channel_id()
    }

    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.channel.dst_channel_id()
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, Error> {
        let client = ForeignClient {
            id: self.dst_client_id().clone(),
            dst_chain: self.dst_chain(),
            src_chain: self.src_chain(),
        };
        client.build_update_client(height)
    }

    pub fn build_update_client_on_src(&self, height: Height) -> Result<Vec<Any>, Error> {
        let client = ForeignClient {
            id: self.src_client_id().clone(),
            dst_chain: self.src_chain(),
            src_chain: self.dst_chain(),
        };
        client.build_update_client(height)
    }

    fn handle_packet_event(&mut self, event: &IBCEvent) -> Result<(), LinkError> {
        let (packet, timeout) =
            handle_packet_event(self.dst_chain(), self.dst_height, self.src_chain(), event)?;

        if let Some(msg) = packet {
            self.packet_msgs.append(&mut vec![msg]);
            self.dst_msgs_input_events.append(&mut vec![event.clone()]);
        }

        if let Some(msg) = timeout {
            self.timeout_msgs.append(&mut vec![msg]);
            self.src_msgs_input_envens.append(&mut vec![event.clone()]);
        }
        Ok(())
    }

    // Determines if the event received is relevant and should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn collect_event(&mut self, event: &IBCEvent) {
        match event {
            IBCEvent::SendPacketChannel(send_packet_ev) => {
                if self.src_channel_id().clone() == send_packet_ev.packet.source_channel
                    && self.src_port_id().clone() == send_packet_ev.packet.source_port
                {
                    self.all_events.append(&mut vec![event.clone()]);
                }
            }
            IBCEvent::WriteAcknowledgementChannel(write_ack_ev) => {
                if self.channel.src_channel_id().clone() == write_ack_ev.packet.destination_channel
                    && self.channel.src_port_id().clone() == write_ack_ev.packet.destination_port
                {
                    self.all_events.append(&mut vec![event.clone()]);
                }
            }
            _ => {}
        };

        if !self.all_events.is_empty() {
            // TODO add ICS height to IBC event
            // All events are at the same height
            self.src_height = Height {
                revision_height: u64::from(self.all_events[0].height()),
                revision_number: ChainId::chain_version(self.src_chain.id().to_string().as_str()),
            };
        }
    }

    fn send_update_client_and_msgs(&mut self) -> Result<(), LinkError> {
        if self.all_events.is_empty() {
            return Ok(());
        }

        if !self.dst_msgs_input_events.is_empty() {
            let update_height = self.src_height.increment();
            let mut msgs_to_send = self.build_update_client_on_dst(update_height)?;
            msgs_to_send.append(&mut self.packet_msgs);
            info!(
                "sending {:?} messages to {}, update client at height {:?}",
                msgs_to_send.len(),
                self.dst_chain.id(),
                update_height,
            );
            let events = self.dst_chain.send_msgs(msgs_to_send)?;
            info!("result {:?}\n", events);

            let ev = events
                .into_iter()
                .find(|event| matches!(event, IBCEvent::ChainError(_)));
            match ev {
                Some(_e) => {}
                None => {
                    self.dst_msgs_input_events = vec![];
                    self.all_events = self.src_msgs_input_envens.clone();
                }
            }
        }

        if !self.src_msgs_input_envens.is_empty() {
            let update_height = self.dst_height.increment();
            let mut msgs_to_send = self.build_update_client_on_src(update_height)?;
            msgs_to_send.append(&mut self.timeout_msgs);
            info!(
                "sending {:?} messages to {}, update client at height {:?}",
                msgs_to_send.len(),
                self.src_chain.id(),
                update_height,
            );
            let events = self.src_chain.send_msgs(msgs_to_send)?;
            info!("result {:?}\n", events);

            let ev = events
                .into_iter()
                .find(|event| matches!(event, IBCEvent::ChainError(_)));
            match ev {
                Some(_e) => {}
                None => {
                    self.src_msgs_input_envens = vec![];
                    self.all_events = self.dst_msgs_input_events.clone();
                }
            }
        }
        Ok(())
    }

    fn relay_from_events(&mut self) -> Result<(), LinkError> {
        // Iterate through the IBC Events, build the message for each and collect all at same height.
        // Send a multi message transaction with these, prepending the client update
        for batch in self.subscription.try_iter().collect::<Vec<_>>().iter() {
            for event in batch.events.iter() {
                self.collect_event(event);
            }

            for _i in 0..MAX_ITER {
                self.dst_height = self.dst_chain.query_latest_height()?;
                for event in self.all_events.clone() {
                    self.handle_packet_event(&event)?;
                }

                let res = self.send_update_client_and_msgs();
                if self.all_events.is_empty() || res.is_err() {
                    break;
                }
            }
        }
        Ok(())
    }
}

pub struct BidirectionalLink {
    pub a_to_b: Link,
    pub b_to_a: Link,
}

impl BidirectionalLink {
    pub fn new(channel: Channel) -> Result<BidirectionalLink, LinkError> {
        let a_chain = channel.src_chain();
        let b_chain = channel.dst_chain();

        Ok(BidirectionalLink {
            a_to_b: Link::new(a_chain.clone(), b_chain.clone(), channel.clone())?,
            b_to_a: Link::new(b_chain, a_chain, channel.flipped())?,
        })
    }

    pub fn run(&mut self) -> Result<(), LinkError> {
        info!("relaying packets for link {:#?}", self.a_to_b.channel);
        loop {
            self.a_to_b.relay_from_events()?;
            self.b_to_a.relay_from_events()?;
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
            info!("{} => event {}", src_chain.id(), send_packet_ev);
            Ok(build_recv_or_timeout_from_send_packet_event(
                dst_chain,
                dst_height,
                src_chain,
                &send_packet_ev,
            )?)
        }
        IBCEvent::WriteAcknowledgementChannel(write_ack_ev) => {
            info!("{} => event {}", src_chain.id(), write_ack_ev);
            Ok((
                Some(build_ack_from_recv_event(
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
            packet.sequence,
            height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg = MsgRecvPacket::new(packet.clone(), proofs.clone(), signer).map_err(|e| {
        Kind::RecvPacket(
            packet.source_channel.clone(),
            "error while building the recv packet".to_string(),
        )
        .context(e)
    })?;

    info!(
        "built recv_packet msg {}, proofs at height {:?}",
        msg.packet,
        proofs.height()
    );

    Ok(msg.to_any::<RawMsgRecvPacket>())
}

fn build_ack_packet(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    event: &WriteAcknowledgement,
    height: Height,
) -> Result<Any, Error> {
    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let packet = event.packet.clone();
    let (_, proofs) = src_chain
        .build_packet_proofs(
            PacketMsgType::Ack,
            &packet.destination_port,
            &packet.destination_channel,
            packet.sequence,
            height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg = MsgAcknowledgement::new(packet.clone(), event.ack.clone(), proofs.clone(), signer)
        .map_err(|e| {
            Kind::AckPacket(
                packet.destination_channel.clone(),
                "error while building the ack packet".to_string(),
            )
            .context(e)
        })?;

    info!(
        "built acknowledgment msg {}, proofs at height {:?}",
        msg.packet,
        proofs.height()
    );

    Ok(msg.to_any::<RawMsgAck>())
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
            &packet.destination_port,
            &packet.destination_channel,
            packet.sequence,
            height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg =
        MsgTimeout::new(packet.clone(), packet.sequence, proofs.clone(), signer).map_err(|e| {
            Kind::TimeoutPacket(
                packet.source_channel.clone(),
                "error while building the timeout packet".to_string(),
            )
            .context(e)
        })?;

    info!(
        "built timeout msg {}, proofs at height {:?}",
        msg.packet,
        proofs.height()
    );

    Ok(msg.to_any::<RawMsgTimeout>())
}

fn build_recv_or_timeout_from_send_packet_event(
    dst_chain: Box<dyn ChainHandle>,
    _dst_height: Height,
    src_chain: Box<dyn ChainHandle>,
    event: &SendPacket,
) -> Result<(Option<Any>, Option<Any>), Error> {
    let packet = event.packet.clone();

    // TODO - change event types to return ICS height
    let event_height = Height::new(
        ChainId::chain_version(src_chain.id().to_string().as_str()),
        u64::from(event.height),
    );

    let dst_height = dst_chain.query_latest_height()?;
    if packet.timeout_height != Height::zero() && packet.timeout_height < dst_height {
        Ok((
            None,
            Some(build_timeout_packet(
                src_chain,
                dst_chain.clone(),
                &event.packet,
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
                &event.packet,
                event_height,
            )?),
            None,
        ))
    }
}

fn build_ack_from_recv_event(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    event: &WriteAcknowledgement,
) -> Result<Any, Error> {
    // TODO - change event types to return ICS height
    let event_height = Height::new(
        ChainId::chain_version(src_chain.id().to_string().as_str()),
        u64::from(event.height),
    );

    build_ack_packet(dst_chain, src_chain, &event, event_height)
}

struct PacketMsgCollector {
    packet_dst_chain: Box<dyn ChainHandle>,
    packet_src_chain: Box<dyn ChainHandle>,
    opts: PacketEnvelope,
    recv_seqs: Vec<Sequence>,
    ack_seqs: Vec<Sequence>,
    src_query_height: Height, // proof height for recv packets
    dst_msgs: Vec<Any>,       // recv packets to be send to destination chain
    dst_query_height: Height, // proof height for acks and timeout
    src_msgs: Vec<Any>,       // acks and/or timeouts to be sent to source chain
}

impl PacketMsgCollector {
    fn new(
        packet_dst_chain: Box<dyn ChainHandle>,
        packet_src_chain: Box<dyn ChainHandle>,
        opts: PacketEnvelope,
    ) -> Self {
        PacketMsgCollector {
            packet_src_chain,
            packet_dst_chain,
            opts,
            recv_seqs: vec![],
            ack_seqs: vec![],
            dst_query_height: Default::default(),
            src_msgs: vec![],
            src_query_height: Default::default(),
            dst_msgs: vec![],
        }
    }

    fn target_height_and_sequences_of_recv_packets(&mut self) -> Result<(), Error> {
        // Query packet commitments on packet's source chain (sent but not acknowledged)
        let pc_request = QueryPacketCommitmentsRequest {
            port_id: self.opts.packet_src_port_id.to_string(),
            channel_id: self.opts.packet_src_channel_id.to_string(),
            pagination: None,
        };
        let (packet_commitments, query_height) =
            self.packet_src_chain.query_packet_commitments(pc_request)?;
        if packet_commitments.is_empty() {
            return Ok(());
        }
        self.src_query_height = query_height;
        let commit_sequences = packet_commitments.iter().map(|p| p.sequence).collect();
        info!(
            "packets that still have commitments on source {}: {:?}",
            self.packet_src_chain.id(),
            commit_sequences
        );

        // Get the packets that have not been received on destination chain
        let request = QueryUnreceivedPacketsRequest {
            port_id: self.opts.packet_dst_port_id.to_string(),
            channel_id: self.opts.packet_dst_channel_id.to_string(),
            packet_commitment_sequences: commit_sequences,
        };

        self.recv_seqs = self
            .packet_dst_chain
            .query_unreceived_packets(request)?
            .into_iter()
            .map(From::from)
            .collect();
        info!(
            "recv packets to send out of the ones with commitments on source {:?}",
            self.recv_seqs
        );

        Ok(())
    }

    fn target_height_and_sequences_of_ack_packets(&mut self) -> Result<(), Error> {
        // Get the sequences of packets that have been acknowledged on destination
        let pc_request = QueryPacketAcknowledgementsRequest {
            port_id: self.opts.packet_dst_port_id.to_string(),
            channel_id: self.opts.packet_dst_channel_id.to_string(),
            pagination: None,
        };
        let (acks_on_destination, query_height) = self
            .packet_dst_chain
            .query_packet_acknowledgements(pc_request)?;

        if acks_on_destination.is_empty() {
            return Ok(());
        }

        let acked_sequences = acks_on_destination.iter().map(|p| p.sequence).collect();
        info!(
            "packets that have acknowledgments on destination {} {:?}",
            self.packet_dst_chain.id(),
            acked_sequences
        );

        let request = QueryUnreceivedAcksRequest {
            port_id: self.opts.packet_src_port_id.to_string(),
            channel_id: self.opts.packet_src_channel_id.to_string(),
            packet_ack_sequences: acked_sequences,
        };

        self.ack_seqs = self
            .packet_src_chain
            .query_unreceived_acknowledgement(request)?
            .into_iter()
            .map(From::from)
            .collect();
        info!(
            "ack packets to send out to {} of the ones with acknowledgments on destination {}: {:?}",
            self.packet_src_chain.id(),
            self.packet_dst_chain.id(),
            self.ack_seqs
        );

        self.dst_query_height = query_height;
        Ok(())
    }

    fn build_recv_packet_and_timeout_msgs(&mut self) -> Result<(), Error> {
        // Get the sequences of packets that have been sent on source chain but
        // have not been received on destination chain (i.e. ack was not seen on source chain)
        self.target_height_and_sequences_of_recv_packets()?;

        if self.recv_seqs.is_empty() {
            return Ok(());
        }

        let mut events = self
            .packet_src_chain
            .query_txs(QueryPacketEventDataRequest {
                event_id: IBCEventType::SendPacket,
                source_port_id: self.opts.packet_src_port_id.clone(),
                source_channel_id: self.opts.packet_src_channel_id.clone(),
                sequences: self.recv_seqs.clone(),
                height: self.src_query_height,
            })?;

        let mut packet_sequences = vec![];
        for event in events.iter() {
            let send_event = downcast!(event => IBCEvent::SendPacketChannel).ok_or_else(|| {
                Kind::Query("packet events".into()).context("unexpected query tx response")
            })?;
            packet_sequences.append(&mut vec![send_event.packet.sequence]);
        }
        info!("received from query_txs {:?}", packet_sequences);

        self.dst_query_height = self.packet_dst_chain.query_latest_height()?;

        for event in events.iter_mut() {
            event.set_height(self.src_query_height);

            let (recv, timeout) = handle_packet_event(
                self.packet_dst_chain.clone(),
                self.dst_query_height,
                self.packet_src_chain.clone(),
                event,
            )?;
            if let Some(recv) = recv {
                self.dst_msgs.append(&mut vec![recv]);
            }
            if let Some(timeout) = timeout {
                self.src_msgs.append(&mut vec![timeout]);
            }
        }
        Ok(())
    }

    fn build_packet_ack_msgs(&mut self) -> Result<(), Error> {
        // Get the sequences of packets that have been acknowledged on destination chain but still
        // have commitments on source chain (i.e. ack was not seen on source chain)
        self.target_height_and_sequences_of_ack_packets()?;

        if self.ack_seqs.is_empty() {
            return Ok(());
        }

        let mut events = self
            .packet_dst_chain
            .query_txs(QueryPacketEventDataRequest {
                event_id: IBCEventType::WriteAck,
                source_port_id: self.opts.packet_src_port_id.clone(),
                source_channel_id: self.opts.packet_src_channel_id.clone(),
                sequences: self.ack_seqs.clone(),
                height: self.dst_query_height,
            })?;

        let mut packet_sequences = vec![];
        for event in events.iter() {
            let write_ack_event = downcast!(event => IBCEvent::WriteAcknowledgementChannel)
                .ok_or_else(|| {
                    Kind::Query("packet events".into()).context("unexpected query tx response")
                })?;
            packet_sequences.append(&mut vec![write_ack_event.packet.sequence]);
        }
        info!("received from query_txs {:?}", packet_sequences);

        self.src_query_height = self.packet_src_chain.query_latest_height()?;
        for event in events.iter_mut() {
            event.set_height(self.dst_query_height);
            if let (Some(new_msg), _) = handle_packet_event(
                self.packet_src_chain.clone(),
                self.src_query_height,
                self.packet_dst_chain.clone(),
                event,
            )? {
                self.src_msgs.append(&mut vec![new_msg]);
            }
        }
        Ok(())
    }

    fn build_client_updates(&mut self) -> Result<(), Error> {
        if !self.dst_msgs.is_empty() {
            // Check that the channel on the destination chain is Open
            verify_channel_state(
                self.packet_dst_chain.clone(),
                &self.opts.packet_dst_port_id,
                &self.opts.packet_dst_channel_id,
            )?;

            // Prepend client updates and send all recv_packet messages
            let mut dst_msgs = build_update_client(
                self.packet_dst_chain.clone(),
                self.packet_src_chain.clone(),
                &self.opts.packet_dst_client_id.clone(),
                self.src_query_height.increment(),
            )?;
            dst_msgs.append(&mut self.dst_msgs);
            self.dst_msgs = dst_msgs;
        }

        if !self.src_msgs.is_empty() {
            // Check the channel on source chain is Open
            verify_channel_state(
                self.packet_src_chain.clone(),
                &self.opts.packet_src_port_id,
                &self.opts.packet_src_channel_id,
            )?;

            // Prepend client updates and send all ack and timeout messages
            let mut src_msgs = build_update_client(
                self.packet_src_chain.clone(),
                self.packet_dst_chain.clone(),
                &self.opts.packet_src_client_id.clone(),
                self.dst_query_height.increment(),
            )?;
            src_msgs.append(&mut self.src_msgs);
            self.src_msgs = src_msgs;
        }
        Ok(())
    }
}

fn verify_channel_state(
    chain: Box<dyn ChainHandle>,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<(), Error> {
    // Check that the packet's channel on source chain is Open
    let channel = chain
        .query_channel(port_id, channel_id, Height::default())
        .map_err(|e| {
            Kind::Packet(
                channel_id.clone(),
                format!("channel does not exist on {}", chain.id()),
            )
            .context(e)
        })?;

    if !channel.state_matches(&State::Open) {
        return Err(Kind::AckPacket(
            channel_id.clone(),
            format!("channel on chain {} not in open state", chain.id()),
        )
        .into());
    }
    Ok(())
}

pub fn build_and_send_recv_packet_messages(
    packet_src_chain: Box<dyn ChainHandle>, // the chain that sourced the packet and where recv proofs are collected
    packet_dst_chain: Box<dyn ChainHandle>, // the chain where recv is sent and from where ack data and proofs are collected
    opts: &PacketOptions,
) -> Result<Vec<IBCEvent>, Error> {
    let mut msg_collector = PacketMsgCollector::new(
        packet_dst_chain.clone(),
        packet_src_chain.clone(),
        opts.packet_envelope.clone(),
    );

    msg_collector.build_recv_packet_and_timeout_msgs()?;
    msg_collector.build_client_updates()?;
    let mut result = vec![];

    if !msg_collector.dst_msgs.is_empty() {
        result.append(&mut packet_dst_chain.send_msgs(msg_collector.dst_msgs)?);
    }

    if !msg_collector.src_msgs.is_empty() {
        result.append(&mut packet_src_chain.send_msgs(msg_collector.src_msgs)?);
    }
    Ok(result)
}

pub fn build_and_send_ack_packet_messages(
    packet_src_chain: Box<dyn ChainHandle>, // the chain that sourced the packet and where ack is sent
    packet_dst_chain: Box<dyn ChainHandle>, // the chain from where ack data and proofs are collected
    opts: &PacketOptions,
) -> Result<Vec<IBCEvent>, Error> {
    let mut msg_collector = PacketMsgCollector::new(
        packet_dst_chain.clone(),
        packet_src_chain.clone(),
        opts.packet_envelope.clone(),
    );
    // Construct the ack messages and get the height of their proofs
    msg_collector.build_packet_ack_msgs()?;
    msg_collector.build_client_updates()?;
    let mut result = vec![];

    if !msg_collector.src_msgs.is_empty() {
        result.append(&mut packet_src_chain.send_msgs(msg_collector.src_msgs)?);
    }
    Ok(result)
}

#[derive(Clone, Debug)]
pub struct PacketEnvelope {
    pub packet_src_client_id: ClientId,
    pub packet_src_port_id: PortId,
    pub packet_src_channel_id: ChannelId,
    pub packet_dst_client_id: ClientId,
    pub packet_dst_port_id: PortId,
    pub packet_dst_channel_id: ChannelId,
}

#[derive(Clone, Debug)]
pub struct PacketOptions {
    pub packet_src_chain_config: ChainConfig,
    pub packet_dst_chain_config: ChainConfig,
    pub packet_envelope: PacketEnvelope,
}
