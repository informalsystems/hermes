use std::thread;
use std::time::Duration;

use prost_types::Any;
use thiserror::Error;
use tracing::{error, info};

use ibc::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
use ibc::ics04_channel::msgs::timeout_on_close::MsgTimeoutOnClose;
use ibc::{
    downcast,
    events::{IBCEvent, IBCEventType},
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::channel::{QueryPacketEventDataRequest, State as ChannelState},
    ics04_channel::events::{SendPacket, WriteAcknowledgement},
    ics04_channel::msgs::acknowledgement::MsgAcknowledgement,
    ics04_channel::msgs::recv_packet::MsgRecvPacket,
    ics04_channel::msgs::timeout::MsgTimeout,
    ics04_channel::packet::{Packet, PacketMsgType, Sequence},
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    tx_msg::Msg,
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    MsgAcknowledgement as RawMsgAck, MsgChannelCloseConfirm as RawMsgChannelCloseConfirm,
    MsgRecvPacket as RawMsgRecvPacket, MsgTimeout as RawMsgTimeout,
    MsgTimeoutOnClose as RawMsgTimeoutOnClose, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};

use crate::chain::handle::{ChainHandle, Subscription};
use crate::channel::{Channel, ChannelError, ChannelSide};
use crate::connection::ConnectionError;
use crate::error::Error;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::relay::MAX_ITER;
use ibc::ics04_channel::channel::State;
use ibc::ics04_channel::events::CloseInit;

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
}

pub struct RelayPath {
    src_chain: Box<dyn ChainHandle>,
    dst_chain: Box<dyn ChainHandle>,
    subscription: Subscription,
    channel: Channel,
    all_events: Vec<IBCEvent>,
    src_height: Height,
    dst_height: Height,
    dst_msgs_input_events: Vec<IBCEvent>,
    src_msgs_input_events: Vec<IBCEvent>,
    packet_msgs: Vec<Any>,
    timeout_msgs: Vec<Any>,
}

impl RelayPath {
    fn new(
        src_chain: Box<dyn ChainHandle>,
        dst_chain: Box<dyn ChainHandle>,
        channel: Channel,
    ) -> Result<Self, LinkError> {
        Ok(RelayPath {
            src_chain: src_chain.clone(),
            dst_chain: dst_chain.clone(),
            subscription: src_chain.subscribe()?,
            channel,
            all_events: vec![],
            src_height: Height::zero(),
            dst_height: Height::zero(),
            dst_msgs_input_events: vec![],
            src_msgs_input_events: vec![],
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
        event: &IBCEvent,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        match event {
            IBCEvent::CloseInitChannel(close_init_ev) => {
                info!("{} => event {}", self.src_chain.id(), close_init_ev);
                Ok((
                    Some(self.build_chan_close_confirm_from_close_init_event(&close_init_ev)?),
                    None,
                ))
            }
            IBCEvent::SendPacket(send_packet_ev) => {
                info!("{} => event {}", self.src_chain.id(), send_packet_ev);
                Ok(self.build_recv_or_timeout_from_send_packet_event(&send_packet_ev)?)
            }
            IBCEvent::WriteAcknowledgement(write_ack_ev) => {
                info!("{} => event {}", self.src_chain.id(), write_ack_ev);
                Ok((Some(self.build_ack_from_recv_event(&write_ack_ev)?), None))
            }
            _ => Ok((None, None)),
        }
    }

    fn build_chan_close_confirm_from_close_init_event(
        &self,
        event: &CloseInit,
    ) -> Result<Any, LinkError> {
        // TODO - change event types to return ICS height
        let event_height = Height::new(
            ChainId::chain_version(self.src_chain.id().to_string().as_str()),
            u64::from(*event.height()),
        );

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), self.src_channel_id(), event_height)
            .map_err(|e| ChannelError::Failed(format!("failed to build channel proofs: {}", e)))?;

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        // Build the domain type message
        let new_msg = MsgChannelCloseConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            proofs,
            signer,
        };

        Ok(new_msg.to_any::<RawMsgChannelCloseConfirm>())
    }

    fn handle_packet_event(&mut self, event: &IBCEvent) -> Result<(), LinkError> {
        let (dst_msg, timeout) = self.build_msg_from_event(event)?;

        if let Some(msg) = dst_msg {
            self.packet_msgs.push(msg);
            self.dst_msgs_input_events.push(event.clone());
        }

        if let Some(msg) = timeout {
            self.timeout_msgs.push(msg);
            self.src_msgs_input_events.push(event.clone());
        }

        Ok(())
    }

    // Determines if the events received are relevant and should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn collect_events(&mut self, events: &[IBCEvent]) {
        for event in events.iter() {
            match event {
                IBCEvent::SendPacket(send_packet_ev) => {
                    if self.src_channel_id() == &send_packet_ev.packet.source_channel
                        && self.src_port_id() == &send_packet_ev.packet.source_port
                    {
                        self.all_events.push(event.clone());
                    }
                }
                IBCEvent::WriteAcknowledgement(write_ack_ev) => {
                    if self.channel.src_channel_id() == &write_ack_ev.packet.destination_channel
                        && self.channel.src_port_id() == &write_ack_ev.packet.destination_port
                    {
                        self.all_events.push(event.clone());
                    }
                }
                IBCEvent::CloseInitChannel(chan_close_ev) => {
                    if Some(self.channel.src_channel_id()) == chan_close_ev.channel_id().as_ref()
                        && self.channel.src_port_id() == chan_close_ev.port_id()
                    {
                        self.all_events.push(event.clone());
                    }
                }
                _ => {}
            };
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
        // TODO add ICS height to IBC event
        // All events are at the same height
        let event_height = Height::new(
            ChainId::chain_version(self.src_chain.id().to_string().as_str()),
            u64::from(*self.all_events[0].height()),
        );

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
            self.src_height = event_height;
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
                .for_each(|ev| ev.set_height(&new_height));
        } else {
            self.src_height = event_height;
        }

        Ok(())
    }

    fn reset_buffers(&mut self) {
        self.dst_msgs_input_events = vec![];
        self.src_msgs_input_events = vec![];
        self.packet_msgs = vec![];
        self.timeout_msgs = vec![];
    }

    fn relay_from_events(&mut self) -> Result<(), LinkError> {
        // Iterate through the IBC Events, build the message for each and collect all at same height.
        // Send a multi message transaction with these, prepending the client update
        for batch in self.subscription.try_iter().collect::<Vec<_>>().iter() {
            // collect relevant events in self.all_events
            self.collect_events(&batch.events);
            self.adjust_events_height()?;

            if self.all_events.is_empty() {
                continue;
            }

            for _i in 0..MAX_ITER {
                self.reset_buffers();

                self.dst_height = self
                    .dst_chain
                    .query_latest_height()
                    .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))?;

                for event in self.all_events.clone() {
                    println!("{} => {:?}", self.src_chain.id(), event);
                    self.handle_packet_event(&event)?;
                }

                let res = self.send_update_client_and_msgs();
                println!("\nresult {:?}", res);

                if self.all_events.is_empty() {
                    break;
                }

                println!("retrying");
            }

            // TODO - add error
            self.all_events = vec![];
        }
        Ok(())
    }

    fn send_update_client_and_msgs(&mut self) -> Result<(Vec<IBCEvent>, Vec<IBCEvent>), LinkError> {
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
                .find(|event| matches!(event, IBCEvent::ChainError(_)));

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
                .find(|event| matches!(event, IBCEvent::ChainError(_)));

            if let Some(_e) = ev {
                self.all_events
                    .append(&mut self.dst_msgs_input_events.clone());
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
        self.src_height = query_height;
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

        self.all_events = self.src_chain.query_txs(QueryPacketEventDataRequest {
            event_id: IBCEventType::SendPacket,
            source_port_id: self.src_port_id().clone(),
            source_channel_id: self.src_channel_id().clone(),
            destination_port_id: self.dst_port_id().clone(),
            destination_channel_id: self.dst_channel_id().clone(),
            sequences,
            height: self.src_height,
        })?;

        let mut packet_sequences = vec![];
        for event in self.all_events.iter() {
            let send_event = downcast!(event => IBCEvent::SendPacket)
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

        self.src_height = query_height;

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
            .query_txs(QueryPacketEventDataRequest {
                event_id: IBCEventType::WriteAck,
                source_port_id: self.dst_port_id().clone(),
                source_channel_id: self.dst_channel_id().clone(),
                destination_port_id: self.src_port_id().clone(),
                destination_channel_id: self.src_channel_id().clone(),
                sequences,
                height: query_height,
            })
            .map_err(|e| LinkError::QueryError(self.src_chain.id(), e))?;

        let mut packet_sequences = vec![];
        for event in self.all_events.iter() {
            let write_ack_event = downcast!(event => IBCEvent::WriteAcknowledgement)
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
        self.dst_height = self
            .dst_chain
            .query_latest_height()
            .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))?;

        for event in self.all_events.iter_mut() {
            event.set_height(&self.src_height);
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
        self.dst_height = self
            .dst_chain
            .query_latest_height()
            .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))?;

        for event in self.all_events.iter_mut() {
            event.set_height(&self.src_height);
        }
        for event in self.all_events.clone() {
            self.handle_packet_event(&event)?;
        }
        Ok(())
    }

    fn build_recv_packet(&self, packet: &Packet, height: Height) -> Result<Any, LinkError> {
        // Get signer
        let signer = self.dst_chain.get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from dst chain {} with error: {}",
                self.dst_chain.id(),
                e
            ))
        })?;

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

        let msg = MsgRecvPacket::new(packet.clone(), proofs.clone(), signer).map_err(|e| {
            LinkError::Failed(format!(
                "error while building the recv packet for src channel {} due to error {}",
                packet.source_channel.clone(),
                e
            ))
        })?;

        info!(
            "built recv_packet msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any::<RawMsgRecvPacket>())
    }

    fn build_ack_packet(
        &self,
        event: &WriteAcknowledgement,
        height: Height,
    ) -> Result<Any, LinkError> {
        // Get signer
        let signer = self.dst_chain.get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from dst chain {} with error: {}",
                self.dst_chain.id(),
                e
            ))
        })?;

        let packet = event.packet.clone();
        let (_, proofs) = self
            .src_chain
            .build_packet_proofs(
                PacketMsgType::Ack,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.src_chain.id(), e))?;

        let msg =
            MsgAcknowledgement::new(packet.clone(), event.ack.clone(), proofs.clone(), signer)
                .map_err(|e| {
                    LinkError::Failed(format!(
                        "error while building the ack packet for dst channel {} due to error {}",
                        packet.destination_channel.clone(),
                        e
                    ))
                })?;

        info!(
            "built acknowledgment msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any::<RawMsgAck>())
    }

    fn build_timeout_packet(&self, packet: &Packet, height: Height) -> Result<Any, LinkError> {
        // Get signer
        let signer = self.src_chain.get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from src chain {} with error: {}",
                self.src_chain.id(),
                e
            ))
        })?;

        let (_, proofs) = self
            .dst_chain
            .build_packet_proofs(
                PacketMsgType::Timeout,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.dst_chain.id(), e))?;

        let msg = MsgTimeout::new(packet.clone(), packet.sequence, proofs.clone(), signer)
            .map_err(|e| {
                LinkError::Failed(format!(
                    "error while building the timeout packet for src channel {} due to error {}",
                    packet.source_channel.clone(),
                    e
                ))
            })?;

        info!(
            "built timeout msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any::<RawMsgTimeout>())
    }

    fn build_timeout_on_close_packet(
        &self,
        packet: &Packet,
        height: Height,
    ) -> Result<Any, LinkError> {
        // Get signer
        let signer = self.src_chain.get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from src chain {} with error: {}",
                self.src_chain.id(),
                e
            ))
        })?;

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

        let msg = MsgTimeoutOnClose::new(packet.clone(), packet.sequence, proofs.clone(), signer)
            .map_err(|e| {
            LinkError::Failed(format!(
                "error while building the timeout packet for src channel {} due to error {}",
                packet.source_channel.clone(),
                e
            ))
        })?;

        info!(
            "built timeout on close msg {}, proofs at height {:?}",
            msg.packet,
            proofs.height()
        );

        Ok(msg.to_any::<RawMsgTimeoutOnClose>())
    }

    fn build_recv_or_timeout_from_send_packet_event(
        &self,
        event: &SendPacket,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        let packet = event.packet.clone();

        // TODO - change event types to return ICS height
        let event_height = Height::new(
            ChainId::chain_version(self.src_chain.id().to_string().as_str()),
            u64::from(event.height),
        );

        let dst_channel = self
            .dst_chain
            .query_channel(self.dst_port_id(), self.dst_channel_id(), self.dst_height)
            .map_err(|e| LinkError::QueryError(self.dst_chain.id(), e))?;

        if dst_channel.state_matches(&ChannelState::Closed) {
            Ok((
                None,
                Some(self.build_timeout_on_close_packet(&event.packet, self.dst_height)?),
            ))
        } else if packet.timeout_height != Height::zero() && packet.timeout_height < self.dst_height
        {
            Ok((
                None,
                Some(self.build_timeout_packet(&event.packet, self.dst_height)?),
            ))
        // } else if packet.timeout_timestamp != 0 && packet.timeout_timestamp < dst_chain.query_time() {
        //     TODO - add query to get the current chain time
        } else {
            Ok((
                Some(self.build_recv_packet(&event.packet, event_height)?),
                None,
            ))
        }
    }

    fn build_ack_from_recv_event(&self, event: &WriteAcknowledgement) -> Result<Any, LinkError> {
        // TODO - change event types to return ICS height
        let event_height = Height::new(
            ChainId::chain_version(self.src_chain.id().to_string().as_str()),
            u64::from(event.height),
        );

        self.build_ack_packet(&event, event_height)
    }
}

pub struct Link {
    pub a_to_b: RelayPath,
    pub b_to_a: RelayPath,
}

#[derive(Clone, Debug)]
pub struct LinkParameters {
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

impl Link {
    pub fn new(channel: Channel) -> Result<Link, LinkError> {
        let a_chain = channel.src_chain();
        let b_chain = channel.dst_chain();

        Ok(Link {
            a_to_b: RelayPath::new(a_chain.clone(), b_chain.clone(), channel.clone())?,
            b_to_a: RelayPath::new(b_chain, a_chain, channel.flipped())?,
        })
    }

    pub fn relay(&mut self) -> Result<(), LinkError> {
        println!("relaying packets on {:#?}", self.a_to_b.channel);
        loop {
            if self.is_closed()? {
                println!("channel is closed, exiting");
                return Ok(());
            }
            self.a_to_b.relay_from_events()?;
            self.b_to_a.relay_from_events()?;

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

        if a_channel.state_matches(&State::Closed) && b_channel.state_matches(&State::Closed) {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn new_from_opts(
        a_chain: Box<dyn ChainHandle>,
        b_chain: Box<dyn ChainHandle>,
        opts: &LinkParameters,
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
        Ok(Link::new(channel)?)
    }

    pub fn build_and_send_recv_packet_messages(&mut self) -> Result<Vec<IBCEvent>, LinkError> {
        self.a_to_b.build_recv_packet_and_timeout_msgs()?;
        let (mut dst_res, mut src_res) = self.a_to_b.send_update_client_and_msgs()?;
        dst_res.append(&mut src_res);
        Ok(dst_res)
    }

    pub fn build_and_send_ack_packet_messages(&mut self) -> Result<Vec<IBCEvent>, LinkError> {
        self.a_to_b.build_packet_ack_msgs()?;
        let (mut dst_res, mut src_res) = self.a_to_b.send_update_client_and_msgs()?;
        dst_res.append(&mut src_res);
        Ok(dst_res)
    }
}
