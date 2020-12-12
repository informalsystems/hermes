use prost_types::Any;
use thiserror::Error;
use tracing::{error, info};

use ibc_proto::ibc::core::channel::v1::{
    MsgRecvPacket as RawMsgRecvPacket, QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

use ibc::{
    downcast,
    events::{IBCEvent, IBCEventType},
    ics04_channel::channel::{QueryPacketEventDataRequest, State},
    ics04_channel::events::SendPacket,
    ics04_channel::msgs::recv_packet::MsgRecvPacket,
    ics04_channel::packet::Packet,
    ics23_commitment::commitment::CommitmentProofBytes,
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

        // Iterate through the IBC Events, build the message for each and collect all at same height.
        // Send a multi message transaction with these, prepending the client update
        for batch in src_subscription.try_iter().collect::<Vec<_>>().iter() {
            for event in batch.events.iter() {
                if !self.must_process_event(src_chain.clone(), event) {
                    continue;
                }
                let packet_msg = handle_packet_event(dst_chain.clone(), src_chain.clone(), event)?;

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
    src_chain: Box<dyn ChainHandle>,
    event: &IBCEvent,
) -> Result<Option<Any>, Error> {
    match event {
        IBCEvent::SendPacketChannel(send_packet_ev) => {
            info!("received event {:#?}", send_packet_ev.envelope);
            let msg = build_packet_recv_msg_from_send_event(dst_chain, src_chain, &send_packet_ev)
                .unwrap();
            Ok(Some(msg.to_any::<RawMsgRecvPacket>()))
        }
        _ => Ok(None),
    }
}

fn build_packet_recv_msg_from_send_event(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    event: &SendPacket,
) -> Result<MsgRecvPacket, Error> {
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
        u64::from(event.envelope.height),
    );

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let (_, proof) = src_chain
        .proven_packet_commitment(
            &event.envelope.packet_src_port,
            &event.envelope.packet_src_channel,
            event.envelope.packet_sequence,
            event_height,
        )
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let msg = MsgRecvPacket::new(
        packet.clone(),
        CommitmentProofBytes::from(proof),
        event_height.increment(),
        signer,
    )
    .map_err(|e| {
        Kind::PacketRecv(
            packet.source_channel,
            "error while building the recv_packet".to_string(),
        )
        .context(e)
    })?;

    Ok(msg)
}

fn build_packet_recv_msgs(
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
        event_id: IBCEventType::SendPacket,
        port_id: src_port.to_string(),
        channel_id: src_channel_id.to_string(),
        sequences: Vec::from(sequences),
        height: query_height,
    })?;

    let mut packet_sequences = vec![];
    for event in events.iter() {
        let send_event = downcast!(event => IBCEvent::SendPacketChannel)
            .ok_or_else(|| Kind::Query.context("unexpected query tx response"))?;

        packet_sequences.append(&mut vec![send_event.envelope.packet_sequence]);
    }
    info!("received from query_txs {:?}", packet_sequences);

    let mut msgs = vec![];
    for event in events.iter_mut() {
        event.set_height(query_height);
        if let Some(new_msg) = handle_packet_event(dst_chain.clone(), src_chain.clone(), event)? {
            msgs.append(&mut vec![new_msg]);
        }
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

fn target_height_and_sequences_of_recv_packets(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &PacketOptions,
) -> Result<(Vec<u64>, Height), Error> {
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
                "channel does not exist on destination chain".into(),
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
    let (sequences, height) =
        target_height_and_sequences_of_recv_packets(dst_chain.clone(), src_chain.clone(), opts)?;
    if sequences.is_empty() {
        return Ok(vec!["No sent packets on source chain".to_string()]);
    }

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst_client_id.clone(),
        height,
    )?;

    let mut packet_msgs = build_packet_recv_msgs(
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
