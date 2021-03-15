use std::thread;
use std::time::Duration;

use prost_types::Any;
use thiserror::Error;
use tracing::{error, info};

use ibc::query::QueryTxRequest;
use ibc::{
    downcast,
    events::{IbcEvent, IbcEventType},
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::{
        channel::{ChannelEnd, Order, QueryPacketEventDataRequest, State as ChannelState},
        events::{SendPacket, WriteAcknowledgement},
        msgs::{
            acknowledgement::MsgAcknowledgement, chan_close_confirm::MsgChannelCloseConfirm,
            recv_packet::MsgRecvPacket, timeout::MsgTimeout, timeout_on_close::MsgTimeoutOnClose,
        },
        packet::{Packet, PacketMsgType, Sequence},
    },
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    signer::Signer,
    tx_msg::Msg,
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};

use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelError, ChannelSide};
use crate::connection::ConnectionError;
use crate::error::Error;
use crate::event::monitor::EventBatch;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::relay::MAX_ITER;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("failed with underlying error: {0}")]
    Failed(String),

    #[error("failed to construct packet proofs for chain {0} with error: {1}")]
    PacketProofsConstructor(ChainId, Error),

    #[error("failed during query to chain id {0} with underlying error: {1}")]
    QueryError(ChainId, Error),

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),

    #[error("Failed during a client operation: {0}:")]
    ClientError(ForeignClientError),

    #[error("PacketError:")]
    PacketError(#[from] Error),

    #[error("exhausted max number of retries:")]
    RetryError,

    #[error("clearing of old packets failed")]
    OldPacketClearingFailed,
}

pub struct RelayPath {
    src_chain: Box<dyn ChainHandle>,
    dst_chain: Box<dyn ChainHandle>,
    channel: Channel,
    clear_packets: bool,
    all_events: Vec<IbcEvent>,
    src_height: Height,
    dst_height: Height,
    dst_msgs_input_events: Vec<IbcEvent>,
    src_msgs_input_events: Vec<IbcEvent>,
    packet_msgs: Vec<Any>,
    timeout_msgs: Vec<Any>,
}

impl RelayPath {
    fn new(
        src_chain: Box<dyn ChainHandle>,
        dst_chain: Box<dyn ChainHandle>,
        channel: Channel,
    ) -> Self {
        Self {
            src_chain,
            dst_chain,
            channel,
            clear_packets: true,
            all_events: vec![],
            src_height: Height::zero(),
            dst_height: Height::zero(),
            dst_msgs_input_events: vec![],
            src_msgs_input_events: vec![],
            packet_msgs: vec![],
            timeout_msgs: vec![],
        }
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

    fn src_channel(&self) -> Result<ChannelEnd, LinkError> {
        Ok(self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), self.src_height)
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?)
    }

    fn dst_channel(&self) -> Result<ChannelEnd, LinkError> {
        Ok(self
            .dst_chain()
            .query_channel(self.dst_port_id(), self.dst_channel_id(), self.dst_height)
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?)
    }

    fn src_signer(&self) -> Result<Signer, LinkError> {
        self.src_chain.get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from src chain {} with error: {}",
                self.src_chain.id(),
                e
            ))
        })
    }

    fn dst_signer(&self) -> Result<Signer, LinkError> {
        self.dst_chain.get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from dst chain {} with error: {}",
                self.dst_chain.id(),
                e
            ))
        })
    }

    fn dst_latest_height(&self) -> Result<Height, LinkError> {
        self.dst_chain
            .query_latest_height()
            .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))
    }

    fn unordered_channel(&self) -> bool {
        self.channel.ordering == Order::Unordered
    }

    fn ordered_channel(&self) -> bool {
        self.channel.ordering == Order::Ordered
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, LinkError> {
        let client = ForeignClient {
            id: self.dst_client_id().clone(),
            dst_chain: self.dst_chain(),
            src_chain: self.src_chain(),
        };

        client
            .build_update_client(height)
            .map_err(LinkError::ClientError)
    }

    pub fn build_update_client_on_src(&self, height: Height) -> Result<Vec<Any>, LinkError> {
        let client = ForeignClient {
            id: self.src_client_id().clone(),
            dst_chain: self.src_chain(),
            src_chain: self.dst_chain(),
        };

        client
            .build_update_client(height)
            .map_err(LinkError::ClientError)
    }

    fn build_msg_from_event(
        &self,
        event: &IbcEvent,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        match event {
            IbcEvent::CloseInitChannel(close_init_ev) => {
                info!("{} => event {}", self.src_chain.id(), close_init_ev);
                Ok((
                    Some(self.build_chan_close_confirm_from_event(&event)?),
                    None,
                ))
            }
            IbcEvent::TimeoutPacket(timeout_ev) => {
                // When a timeout packet for an ordered channel is processed on-chain (src here)
                // the chain closes the channel but no close init event is emitted, instead
                // we get a timeout packet event (this happens for both unordered and ordered channels)
                // Here we check it the channel is closed on src and send a channel close confirm
                // to the counterparty.
                if self.ordered_channel()
                    && self.src_channel()?.state_matches(&ChannelState::Closed)
                {
                    info!(
                        "{} => event {} closes the channel",
                        self.src_chain.id(),
                        timeout_ev
                    );
                    Ok((
                        Some(self.build_chan_close_confirm_from_event(&event)?),
                        None,
                    ))
                } else {
                    Ok((None, None))
                }
            }
            IbcEvent::SendPacket(send_packet_ev) => {
                info!("{} => event {}", self.src_chain.id(), send_packet_ev);
                Ok(self.build_recv_or_timeout_from_send_packet_event(&send_packet_ev)?)
            }
            IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                info!("{} => event {}", self.src_chain.id(), write_ack_ev);
                Ok((Some(self.build_ack_from_recv_event(&write_ack_ev)?), None))
            }
            _ => Ok((None, None)),
        }
    }

    fn build_chan_close_confirm_from_event(&self, event: &IbcEvent) -> Result<Any, LinkError> {
        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), self.src_channel_id(), event.height())
            .map_err(|e| ChannelError::Failed(format!("failed to build channel proofs: {}", e)))?;

        // Build the domain type message
        let new_msg = MsgChannelCloseConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            proofs,
            signer: self.dst_signer()?,
        };

        Ok(new_msg.to_any())
    }

    fn handle_packet_event(&mut self, event: &IbcEvent) -> Result<(), LinkError> {
        let (dst_msg, timeout) = self.build_msg_from_event(event)?;

        if let Some(msg) = dst_msg {
            self.packet_msgs.push(msg);
            self.dst_msgs_input_events.push(event.clone());
        }

        if let Some(msg) = timeout {
            // For Ordered channels a single timeout event should be sent as this closes the channel.
            // Otherwise a multi message transaction will fail.
            if self.unordered_channel() || self.timeout_msgs.is_empty() {
                self.timeout_msgs.push(msg);
                self.src_msgs_input_events.push(event.clone());
            }
        }

        Ok(())
    }

    // Determines if the events received are relevant and should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn collect_events(&mut self, events: &[IbcEvent]) {
        for event in events.iter() {
            match event {
                IbcEvent::SendPacket(send_packet_ev) => {
                    if self.src_channel_id() == &send_packet_ev.packet.source_channel
                        && self.src_port_id() == &send_packet_ev.packet.source_port
                    {
                        self.all_events.push(event.clone());
                    }
                }
                IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                    if self.channel.src_channel_id() == &write_ack_ev.packet.destination_channel
                        && self.channel.src_port_id() == &write_ack_ev.packet.destination_port
                    {
                        self.all_events.push(event.clone());
                    }
                }
                IbcEvent::CloseInitChannel(chan_close_ev) => {
                    if self.channel.src_channel_id() == chan_close_ev.channel_id()
                        && self.channel.src_port_id() == chan_close_ev.port_id()
                    {
                        self.all_events.push(event.clone());
                    }
                }
                IbcEvent::TimeoutPacket(timeout_ev) => {
                    if self.channel.src_channel_id() == timeout_ev.src_channel_id()
                        && self.channel.src_port_id() == timeout_ev.src_port_id()
                    {
                        self.all_events.push(event.clone());
                    }
                }
                _ => {}
            }
        }

        if !self.all_events.is_empty() {
            // All events are at the same height
            self.src_height = self.all_events[0].height();
        }
    }

    // May adjust the height of events in self.all_events.
    // Checks if the client on destination chain is at a higher height than the event height.
    // This can happen if a client update has happened after the event was emitted but before
    // this point when the relayer starts to process the events.
    fn adjust_events_height(&mut self) -> Result<(), LinkError> {
        if self.all_events.is_empty() {
            return Ok(());
        }

        let event_height = self.src_height;

        // Check if a consensus state at event_height + 1 exists on destination chain already
        // and update src_height
        if self
            .dst_chain()
            .proven_client_consensus(
                self.dst_client_id(),
                event_height.increment(),
                Height::zero(),
            )
            .is_ok()
        {
            return Ok(());
        }

        // Get the latest trusted height from the client state on destination.
        let trusted_height = self
            .dst_chain()
            .query_client_state(self.dst_client_id(), Height::zero())
            .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))?
            .latest_height();

        // event_height + 1 is the height at which the client on destination chain
        // should be updated, unless ...
        if trusted_height > event_height.increment() {
            // ... client is already at a higher height.
            let new_height = trusted_height
                .decrement()
                .map_err(|e| LinkError::Failed(e.to_string()))?;
            self.src_height = new_height;
            self.all_events
                .iter_mut()
                .for_each(|ev| ev.set_height(new_height));
        }

        Ok(())
    }

    fn reset_buffers(&mut self) {
        self.dst_msgs_input_events = vec![];
        self.src_msgs_input_events = vec![];
        self.packet_msgs = vec![];
        self.timeout_msgs = vec![];
    }

    fn relay_pending_packets(&mut self) -> Result<(), LinkError> {
        println!("clearing old packets on {:#?}", self.channel);
        for _i in 0..MAX_ITER {
            if self.build_recv_packet_and_timeout_msgs().is_ok()
                && self.send_update_client_and_msgs().is_ok()
                && self.build_packet_ack_msgs().is_ok()
                && self.send_update_client_and_msgs().is_ok()
            {
                return Ok(());
            }
            self.reset_buffers();
            self.all_events = vec![];
        }
        Err(LinkError::OldPacketClearingFailed)
    }

    pub fn clear_packets(&mut self, height: Height) -> Result<(), LinkError> {
        if self.clear_packets {
            self.src_height = height
                .decrement()
                .map_err(|e| LinkError::Failed(e.to_string()))?;

            self.relay_pending_packets()?;
            self.clear_packets = false;
        }

        Ok(())
    }

    /// Iterate through the IBC Events, build the message for each and collect all at same height.
    /// Send a multi message transaction with these, prepending the client update
    pub fn relay_from_events(&mut self, batch: EventBatch) -> Result<(), LinkError> {
        self.clear_packets(batch.height)?;

        // collect relevant events in self.all_events
        self.collect_events(&batch.events);
        self.adjust_events_height()?;

        if self.all_events.is_empty() {
            return Ok(());
        }

        for _i in 0..MAX_ITER {
            self.reset_buffers();

            self.dst_height = self.dst_latest_height()?;

            // Collect the messages for all events
            for event in self.all_events.clone() {
                println!("{} => {:?}", self.src_chain.id(), event);
                self.handle_packet_event(&event)?;
            }

            // Send client update and messages
            let res = self.send_update_client_and_msgs();
            println!("\nresult {:?}", res);

            if self.all_events.is_empty() {
                break;
            }

            println!("retrying");
        }

        // TODO - add error
        self.all_events = vec![];

        Ok(())
    }

    fn send_update_client_and_msgs(&mut self) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), LinkError> {
        let mut src_tx_events = vec![];
        let mut dst_tx_events = vec![];

        // Clear all_events and collect the src and dst input events if Tx-es fail
        self.all_events = vec![];

        if !self.packet_msgs.is_empty() {
            let update_height = self.src_height.increment();
            let mut msgs_to_send = vec![];

            // Check if a consensus state at update_height exists on destination chain already
            if self
                .dst_chain()
                .proven_client_consensus(self.dst_client_id(), update_height, Height::zero())
                .is_err()
            {
                msgs_to_send = self.build_update_client_on_dst(update_height)?;
                info!("sending update client at height {:?}", update_height,);
            }

            msgs_to_send.append(&mut self.packet_msgs);

            info!(
                "sending {} messages to {}",
                msgs_to_send.len(),
                self.dst_chain.id()
            );

            dst_tx_events = self.dst_chain.send_msgs(msgs_to_send)?;
            info!("result {:?}\n", dst_tx_events);

            let ev = dst_tx_events
                .clone()
                .into_iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));

            if let Some(_e) = ev {
                self.all_events
                    .append(&mut self.dst_msgs_input_events.clone());
            }
        }

        if !self.timeout_msgs.is_empty() {
            let update_height = self.dst_height.increment();
            let mut msgs_to_send = self.build_update_client_on_src(update_height)?;
            msgs_to_send.append(&mut self.timeout_msgs);
            info!(
                "sending {:?} messages to {}, update client at height {:?}",
                msgs_to_send.len(),
                self.src_chain.id(),
                update_height,
            );

            src_tx_events = self.src_chain.send_msgs(msgs_to_send)?;
            info!("result {:?}\n", src_tx_events);

            let ev = src_tx_events
                .clone()
                .into_iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));

            if let Some(_e) = ev {
                self.all_events
                    .append(&mut self.src_msgs_input_events.clone());
            }
        }

        Ok((dst_tx_events, src_tx_events))
    }

    fn target_height_and_send_packet_events(&mut self) -> Result<(), LinkError> {
        // Query packet commitments on source chain that have not been acknowledged
        let pc_request = QueryPacketCommitmentsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: self.src_channel_id().to_string(),
            pagination: None,
        };
        let (packet_commitments, query_height) =
            self.src_chain.query_packet_commitments(pc_request)?;
        if packet_commitments.is_empty() {
            return Ok(());
        }
        if self.src_height == Height::zero() {
            self.src_height = query_height;
        }
        let commit_sequences = packet_commitments.iter().map(|p| p.sequence).collect();
        info!(
            "packets that still have commitments on {}: {:?}",
            self.src_chain.id(),
            commit_sequences
        );

        // Get the packets that have not been received on destination chain
        let request = QueryUnreceivedPacketsRequest {
            port_id: self.dst_port_id().to_string(),
            channel_id: self.dst_channel_id().to_string(),
            packet_commitment_sequences: commit_sequences,
        };

        let sequences: Vec<Sequence> = self
            .dst_chain
            .query_unreceived_packets(request)?
            .into_iter()
            .map(From::from)
            .collect();

        info!(
            "recv packets to send out to {} of the ones with commitments on source{}: {:?}",
            self.dst_chain.id(),
            self.src_chain.id(),
            sequences
        );

        if sequences.is_empty() {
            return Ok(());
        }

        let query = QueryTxRequest::Packet(QueryPacketEventDataRequest {
            event_id: IbcEventType::SendPacket,
            source_port_id: self.src_port_id().clone(),
            source_channel_id: self.src_channel_id().clone(),
            destination_port_id: self.dst_port_id().clone(),
            destination_channel_id: self.dst_channel_id().clone(),
            sequences,
            height: self.src_height,
        });

        self.all_events = self.src_chain.query_txs(query)?;

        let mut packet_sequences = vec![];
        for event in self.all_events.iter() {
            let send_event = downcast!(event => IbcEvent::SendPacket)
                .ok_or_else(|| LinkError::Failed("unexpected query tx response".into()))?;
            packet_sequences.push(send_event.packet.sequence);
        }
        info!("received from query_txs {:?}", packet_sequences);

        Ok(())
    }

    fn target_height_and_write_ack_events(&mut self) -> Result<(), LinkError> {
        // Get the sequences of packets that have been acknowledged on source
        let pc_request = QueryPacketAcknowledgementsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: self.src_channel_id().to_string(),
            pagination: None,
        };
        let (acks_on_source, query_height) = self
            .src_chain
            .query_packet_acknowledgements(pc_request)
            .map_err(|e| LinkError::QueryError(self.src_chain.id(), e))?;

        if acks_on_source.is_empty() {
            return Ok(());
        }

        if self.src_height == Height::zero() {
            self.src_height = query_height;
        }

        let acked_sequences = acks_on_source.iter().map(|p| p.sequence).collect();
        info!(
            "packets that have acknowledgments on {} {:?}",
            self.src_chain.id(),
            acked_sequences
        );

        let request = QueryUnreceivedAcksRequest {
            port_id: self.dst_port_id().to_string(),
            channel_id: self.dst_channel_id().to_string(),
            packet_ack_sequences: acked_sequences,
        };

        let sequences: Vec<Sequence> = self
            .dst_chain
            .query_unreceived_acknowledgement(request)
            .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))?
            .into_iter()
            .map(From::from)
            .collect();
        info!(
            "ack packets to send out to {} of the ones with acknowledgments on {}: {:?}",
            self.dst_chain.id(),
            self.src_chain.id(),
            sequences
        );

        if sequences.is_empty() {
            return Ok(());
        }

        self.all_events = self
            .src_chain
            .query_txs(QueryTxRequest::Packet(QueryPacketEventDataRequest {
                event_id: IbcEventType::WriteAck,
                source_port_id: self.dst_port_id().clone(),
                source_channel_id: self.dst_channel_id().clone(),
                destination_port_id: self.src_port_id().clone(),
                destination_channel_id: self.src_channel_id().clone(),
                sequences,
                height: self.src_height,
            }))
            .map_err(|e| LinkError::QueryError(self.src_chain.id(), e))?;

        let mut packet_sequences = vec![];
        for event in self.all_events.iter() {
            let write_ack_event = downcast!(event => IbcEvent::WriteAcknowledgement)
                .ok_or_else(|| LinkError::Failed("unexpected query tx response".into()))?;
            packet_sequences.push(write_ack_event.packet.sequence);
        }
        info!("received from query_txs {:?}", packet_sequences);
        Ok(())
    }

    fn build_recv_packet_and_timeout_msgs(&mut self) -> Result<(), LinkError> {
        // Get the events for the send packets on source chain that have not been received on
        // destination chain (i.e. ack was not seen on source chain)
        self.target_height_and_send_packet_events()?;
        self.dst_height = self.dst_latest_height()?;

        for event in self.all_events.iter_mut() {
            event.set_height(self.src_height);
        }

        for event in self.all_events.clone() {
            self.handle_packet_event(&event)?;
        }
        Ok(())
    }

    fn build_packet_ack_msgs(&mut self) -> Result<(), LinkError> {
        // Get the sequences of packets that have been acknowledged on destination chain but still
        // have commitments on source chain (i.e. ack was not seen on source chain)
        self.target_height_and_write_ack_events()?;
        self.dst_height = self.dst_latest_height()?;

        for event in self.all_events.iter_mut() {
            event.set_height(self.src_height);
        }
        for event in self.all_events.clone() {
            self.handle_packet_event(&event)?;
        }
        Ok(())
    }

    fn build_recv_packet(&self, packet: &Packet, height: Height) -> Result<Any, LinkError> {
        let (_, proofs) = self
            .src_chain
            .build_packet_proofs(
                PacketMsgType::Recv,
                &packet.source_port,
                &packet.source_channel,
                packet.sequence,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.src_chain.id(), e))?;

        let msg = MsgRecvPacket::new(packet.clone(), proofs.clone(), self.dst_signer()?);

        info!(
            "built recv_packet msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any())
    }

    fn build_ack_from_recv_event(&self, event: &WriteAcknowledgement) -> Result<Any, LinkError> {
        let packet = event.packet.clone();
        let (_, proofs) = self
            .src_chain
            .build_packet_proofs(
                PacketMsgType::Ack,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                event.height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.src_chain.id(), e))?;

        let msg = MsgAcknowledgement::new(
            packet,
            event.ack.clone(),
            proofs.clone(),
            self.dst_signer()?,
        );

        info!(
            "built acknowledgment msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any())
    }

    fn build_timeout_packet(&self, packet: &Packet, height: Height) -> Result<Any, LinkError> {
        let (packet_type, next_sequence_received) = if self.ordered_channel() {
            let next_seq = self
                .dst_chain()
                .query_next_sequence_receive(QueryNextSequenceReceiveRequest {
                    port_id: self.dst_port_id().to_string(),
                    channel_id: self.dst_channel_id().to_string(),
                })
                .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;
            (PacketMsgType::TimeoutOrdered, next_seq)
        } else {
            (PacketMsgType::TimeoutUnordered, packet.sequence)
        };

        let (_, proofs) = self
            .dst_chain
            .build_packet_proofs(
                packet_type,
                &packet.destination_port,
                &packet.destination_channel,
                next_sequence_received,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.dst_chain.id(), e))?;

        let msg = MsgTimeout::new(
            packet.clone(),
            next_sequence_received,
            proofs.clone(),
            self.src_signer()?,
        );

        info!(
            "built timeout msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any())
    }

    fn build_timeout_on_close_packet(
        &self,
        packet: &Packet,
        height: Height,
    ) -> Result<Any, LinkError> {
        let (_, proofs) = self
            .dst_chain
            .build_packet_proofs(
                PacketMsgType::TimeoutOnClose,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.dst_chain.id(), e))?;

        let msg = MsgTimeoutOnClose::new(
            packet.clone(),
            packet.sequence,
            proofs.clone(),
            self.src_signer()?,
        );

        info!(
            "built timeout on close msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any())
    }

    fn build_recv_or_timeout_from_send_packet_event(
        &self,
        event: &SendPacket,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        let packet = event.packet.clone();

        if self.dst_channel()?.state_matches(&ChannelState::Closed) {
            Ok((
                None,
                Some(self.build_timeout_on_close_packet(&event.packet, self.dst_height)?),
            ))
        } else if packet.timeout_height != Height::zero()
            && packet.timeout_height < self.dst_latest_height()?
        {
            Ok((
                None,
                Some(self.build_timeout_packet(&event.packet, self.dst_height)?),
            ))
        // } else if packet.timeout_timestamp != 0 && packet.timeout_timestamp < dst_chain.query_time() {
        //     TODO - add query to get the current chain time
        } else {
            Ok((
                Some(self.build_recv_packet(&event.packet, event.height)?),
                None,
            ))
        }
    }
}

#[derive(Clone, Debug)]
pub struct LinkParameters {
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

pub struct Link {
    pub a_to_b: RelayPath,
    pub b_to_a: RelayPath,
}

impl Link {
    pub fn new(channel: Channel) -> Self {
        let a_chain = channel.src_chain();
        let b_chain = channel.dst_chain();
        let flipped = channel.flipped();

        Self {
            a_to_b: RelayPath::new(a_chain.clone(), b_chain.clone(), channel),
            b_to_a: RelayPath::new(b_chain, a_chain, flipped),
        }
    }

    pub fn relay(&mut self) -> Result<(), LinkError> {
        println!("relaying packets on {:#?}", self.a_to_b.channel);

        let events_a = self.a_to_b.src_chain().subscribe()?;
        let events_b = self.b_to_a.src_chain().subscribe()?;

        loop {
            if self.is_closed()? {
                println!("channel is closed, exiting");
                return Ok(());
            }

            if let Ok(batch) = events_a.try_recv() {
                self.a_to_b.relay_from_events(batch.unwrap_or_clone())?;
            }

            if let Ok(batch) = events_b.try_recv() {
                self.b_to_a.relay_from_events(batch.unwrap_or_clone())?;
            }

            // TODO - select over the two subscriptions
            thread::sleep(Duration::from_millis(100))
        }
    }

    fn is_closed(&self) -> Result<bool, LinkError> {
        let a_channel = self
            .a_to_b
            .src_chain()
            .query_channel(
                self.a_to_b.src_port_id(),
                self.a_to_b.src_channel_id(),
                Height::default(),
            )
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    self.a_to_b.src_channel_id(),
                    self.a_to_b.src_chain().id(),
                    e
                ))
            })?;

        let b_channel = self
            .a_to_b
            .dst_chain()
            .query_channel(
                self.a_to_b.dst_port_id(),
                self.a_to_b.dst_channel_id(),
                Height::default(),
            )
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    self.a_to_b.dst_channel_id(),
                    self.a_to_b.dst_chain().id(),
                    e
                ))
            })?;

        if a_channel.state_matches(&ChannelState::Closed)
            && b_channel.state_matches(&ChannelState::Closed)
        {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn new_from_opts(
        a_chain: Box<dyn ChainHandle>,
        b_chain: Box<dyn ChainHandle>,
        opts: LinkParameters,
    ) -> Result<Link, LinkError> {
        // Check that the packet's channel on source chain is Open
        let a_channel_id = &opts.src_channel_id;
        let a_channel = a_chain
            .query_channel(&opts.src_port_id, a_channel_id, Height::default())
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    a_channel_id.clone(),
                    a_chain.id(),
                    e
                ))
            })?;

        if !a_channel.state_matches(&ChannelState::Open)
            && !a_channel.state_matches(&ChannelState::Closed)
        {
            return Err(LinkError::Failed(format!(
                "channel {} on chain {} not in open or close state when packets and timeouts can be relayed",
                a_channel_id.clone(),
                a_chain.id()
            )));
        }

        let b_channel_id = a_channel.counterparty().channel_id.clone().ok_or_else(|| {
            LinkError::Failed(format!(
                "counterparty channel id not found for {}",
                a_channel_id
            ))
        })?;

        if a_channel.connection_hops().is_empty() {
            return Err(LinkError::Failed(format!(
                "channel {} on chain {} has no connection hops",
                a_channel_id.clone(),
                a_chain.id()
            )));
        }

        let a_connection_id = a_channel.connection_hops()[0].clone();
        let a_connection = a_chain.query_connection(&a_connection_id, Height::zero())?;

        if !a_connection.state_matches(&ConnectionState::Open) {
            return Err(LinkError::Failed(format!(
                "connection for channel {} on chain {} not in open state",
                a_channel_id.clone(),
                a_chain.id()
            )));
        }

        let channel = Channel {
            ordering: Default::default(),
            a_side: ChannelSide::new(
                a_chain,
                a_connection.client_id().clone(),
                a_connection_id,
                opts.src_port_id.clone(),
                opts.src_channel_id.clone(),
            ),
            b_side: ChannelSide::new(
                b_chain,
                a_connection.counterparty().client_id().clone(),
                a_connection.counterparty().connection_id().unwrap().clone(),
                a_channel.counterparty().port_id.clone(),
                b_channel_id,
            ),
        };

        Ok(Link::new(channel))
    }

    pub fn build_and_send_recv_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        self.a_to_b.build_recv_packet_and_timeout_msgs()?;
        let (mut dst_res, mut src_res) = self.a_to_b.send_update_client_and_msgs()?;
        dst_res.append(&mut src_res);
        Ok(dst_res)
    }

    pub fn build_and_send_ack_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        self.a_to_b.build_packet_ack_msgs()?;
        let (mut dst_res, mut src_res) = self.a_to_b.send_update_client_and_msgs()?;
        dst_res.append(&mut src_res);
        Ok(dst_res)
    }
}
