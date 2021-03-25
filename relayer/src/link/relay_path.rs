use std::time::{Duration, Instant};

use prost_types::Any;
use tracing::info;

use ibc::{
    downcast,
    events::{IbcEvent, IbcEventType},
    ics04_channel::{
        channel::{ChannelEnd, Order, QueryPacketEventDataRequest, State as ChannelState},
        events::{SendPacket, WriteAcknowledgement},
        msgs::{
            acknowledgement::MsgAcknowledgement, chan_close_confirm::MsgChannelCloseConfirm,
            recv_packet::MsgRecvPacket, timeout::MsgTimeout, timeout_on_close::MsgTimeoutOnClose,
        },
        packet::{Packet, PacketMsgType, Sequence},
    },
    ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
    signer::Signer,
    tx_msg::Msg,
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};

use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelError};
use crate::event::monitor::EventBatch;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::link::error::LinkError;
use crate::relay::MAX_ITER;
use std::thread;

/// A batch of events that are scheduled for later processing.
pub struct ScheduledBatch {
    /// Stores the time when the clients on src and dest chains have been updated.
    update_time: Instant,

    /// The outstanding batch of events.
    events: Vec<IbcEvent>,

    /// The height which the destination chain has when the batch is scheduled.
    /// The client on source chain was updated with a header corresponding to this height.
    dst_height: Height,
}

pub struct RelayPath {
    src_chain: Box<dyn ChainHandle>,
    dst_chain: Box<dyn ChainHandle>,
    channel: Channel,
    clear_packets: bool,
    all_events: Vec<IbcEvent>,
    dst_msgs_input_events: Vec<IbcEvent>,
    src_msgs_input_events: Vec<IbcEvent>,
    packet_msgs: Vec<Any>,
    timeout_msgs: Vec<Any>,
    scheduled: Vec<ScheduledBatch>,
}

impl RelayPath {
    pub fn new(
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
            dst_msgs_input_events: vec![],
            src_msgs_input_events: vec![],
            packet_msgs: vec![],
            timeout_msgs: vec![],
            scheduled: vec![],
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

    pub fn channel(&self) -> &Channel {
        &self.channel
    }

    fn src_channel(&self, height: Height) -> Result<ChannelEnd, LinkError> {
        Ok(self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), height)
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?)
    }

    fn dst_channel(&self, height: Height) -> Result<ChannelEnd, LinkError> {
        Ok(self
            .dst_chain()
            .query_channel(self.dst_port_id(), self.dst_channel_id(), height)
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

    pub fn dst_latest_height(&self) -> Result<Height, LinkError> {
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

    // TODO(Adi): This needs refactoring!
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
        dst_chain_height: Height,
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
                // Here we check that the channel is closed on src and send a channel close confirm
                // to the counterparty.
                if self.ordered_channel()
                    && self
                        .src_channel(timeout_ev.height)?
                        .state_matches(&ChannelState::Closed)
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
                Ok(self.build_recv_or_timeout_from_send_packet_event(
                    &send_packet_ev,
                    dst_chain_height,
                )?)
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

    /// Builds a message out of an `event`.
    /// Handles building both ordinary `RecvPacket` messages,
    /// as well as channel close handshake (`ChanCloseConfirm`), `WriteAck` messages,
    /// and timeouts messages (`MsgTimeoutOnClose` or `MsgTimeout`).
    ///
    /// The parameter `dst_chain_height` represents the height which the proofs for timeout
    /// messages should target. It is necessary that the client hosted on the source chain
    /// has a consensus state installed corresponding for this height.
    fn handle_packet_event(
        &mut self,
        event: &IbcEvent,
        dst_chain_height: Height,
    ) -> Result<(), LinkError> {
        let (dst_msg, timeout) = self.build_msg_from_event(event, dst_chain_height)?;

        // Collect messages to be sent to the destination chain
        if let Some(msg) = dst_msg {
            self.packet_msgs.push(msg);
            self.dst_msgs_input_events.push(event.clone());
        }

        // Collect timeout messages, to be sent to the source chain
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
    }

    // May adjust the height of events in self.all_events.
    // Checks if the client on destination chain is at a higher height than the event height.
    // This can happen if a client update has happened after the event was emitted but before
    // this point when the relayer starts to process the events.
    fn adjust_events_height(&mut self) -> Result<(), LinkError> {
        if self.all_events.is_empty() {
            return Ok(());
        }

        let event_height = self.all_events[0].height();

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
            if self.relay_recv_packet_and_timeout_msgs().is_ok()
                && self.relay_packet_ack_msgs().is_ok()
            {
                return Ok(());
            }
            self.reset_buffers();
            self.all_events = vec![];
        }
        Err(LinkError::OldPacketClearingFailed)
    }

    /// Should not run more than once per execution.
    pub fn clear_packets(&mut self, _height: Height) -> Result<(), LinkError> {
        if self.clear_packets {
            self.relay_pending_packets()?;
            self.clear_packets = false;
        }

        Ok(())
    }

    /// Iterate through the IBC Events, build the message for each and collect all at same height.
    pub fn relay_from_events(&mut self, batch: EventBatch) -> Result<(), LinkError> {
        self.clear_packets(batch.height)?;

        // Collect relevant events in `self.all_events`.
        self.collect_events(&batch.events);
        self.adjust_events_height()?;

        if self.channel.connection_delay.as_nanos() > 0 {
            self.relay_with_delay()
        } else {
            self.relay_multi_msg()
        }
    }

    /// Sends the client update in a separate transaction from packet messages, allowing for the
    /// delay period to pass between the client update and packet messages.
    fn relay_with_delay(&mut self) -> Result<(), LinkError> {
        // If there are some new events, update src. and dest. clients, then schedule the relaying
        //  of packets corresponding to these events.
        if !self.all_events.is_empty() {
            let dst_update_height = self.dst_latest_height()?;
            self.update_clients(self.all_events[0].height().increment(), dst_update_height)?;

            // Schedule the event batch, and let it sit for a while until the delay period passes
            self.schedule_batch(self.all_events.clone(), dst_update_height);
        }

        // Iterate through all the outstanding event batches that have fulfilled their delay period,
        // and send the packet messages corresponding to these events
        while let Some(batch) = self.try_fetch_scheduled_batch() {
            self.all_events = batch.events;

            for _i in 0..MAX_ITER {
                self.reset_buffers();

                // Collect the messages for all events
                for event in self.all_events.clone() {
                    println!("{} => {:?}", self.src_chain.id(), event);
                    self.handle_packet_event(&event, batch.dst_height)?;
                }

                // Send messages
                let res = self.send_msgs()?;
                println!("\nresult {:?}", res);

                if self.all_events.is_empty() {
                    break;
                }

                println!("retrying");
            }
        }

        self.all_events = vec![];
        Ok(())
    }

    /// Send a multi message transaction with packet messages, prepending the client update.
    /// Ignores any delay period for packets.
    fn relay_multi_msg(&mut self) -> Result<(), LinkError> {
        if self.all_events.is_empty() {
            return Ok(());
        }

        let dst_update_height = self.dst_latest_height()?;

        for _i in 0..MAX_ITER {
            self.reset_buffers();

            // Collect the messages for all events
            for event in self.all_events.clone() {
                println!("{} => {:?}", self.src_chain.id(), event);
                self.handle_packet_event(&event, dst_update_height)?;
            }

            // Send client update and messages
            let res = self.send_update_client_and_msgs(dst_update_height);
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

    /// Picks up all messages that sit in `self.packet_msgs` and `self.timeout_msgs` and sends them
    /// to the destination and source chain, respectively.
    pub fn send_msgs(&mut self) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), LinkError> {
        let mut src_tx_events = vec![];
        let mut dst_tx_events = vec![];

        // Clear this field. We use it to re-collect the src and dst input events if Tx-es fail
        self.all_events = vec![];

        if !self.packet_msgs.is_empty() {
            info!(
                "sending {} messages to {}",
                self.packet_msgs.len(),
                self.dst_chain.id()
            );

            dst_tx_events = self.dst_chain.send_msgs(self.packet_msgs.clone())?;
            info!("result {:?}\n", dst_tx_events);

            let ev = dst_tx_events
                .clone()
                .into_iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));

            // Recycle the original events that produced these messages, we'll retry based on them
            if ev.is_some() {
                self.all_events
                    .append(&mut self.dst_msgs_input_events.clone());
            }
        }

        if !self.timeout_msgs.is_empty() {
            info!(
                "sending {:?} messages to {}",
                self.timeout_msgs.len(),
                self.src_chain.id(),
            );

            src_tx_events = self.src_chain.send_msgs(self.timeout_msgs.clone())?;
            info!("result {:?}\n", src_tx_events);

            let ev = src_tx_events
                .clone()
                .into_iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));

            // Recycle
            if ev.is_some() {
                self.all_events
                    .append(&mut self.src_msgs_input_events.clone());
            }
        }

        Ok((dst_tx_events, src_tx_events))
    }

    /// Sends ClientUpdate transactions ahead of a scheduled batch.
    /// Includes basic retrying and returns failure only after all retries are exhausted.
    pub fn update_clients(
        &self,
        src_chain_height: Height,
        dst_chain_height: Height,
    ) -> Result<(), LinkError> {
        // Handle the update on the destination chain
        // Check if a consensus state at update_height exists on destination chain already
        for i in 0..MAX_ITER {
            if self
                .dst_chain()
                .proven_client_consensus(self.dst_client_id(), src_chain_height, Height::zero())
                .is_err()
            {
                let dst_update = self.build_update_client_on_dst(src_chain_height)?;
                info!("sending update client at height {:?}", src_chain_height);

                let dst_tx_events = self.dst_chain.send_msgs(dst_update)?;
                info!("result {:?}\n", dst_tx_events);

                let dst_err_ev = dst_tx_events
                    .into_iter()
                    .find(|event| matches!(event, IbcEvent::ChainError(_)));

                if let Some(err_ev) = dst_err_ev {
                    // If there was an error and this was the last retry
                    if i == (MAX_ITER - 1) {
                        return Err(LinkError::ClientError(ForeignClientError::ClientUpdate(
                            format!(
                                "Failed to update client on destination {} with err: {:?}",
                                self.dst_chain.id(),
                                err_ev
                            ),
                        )));
                    } // Else: retry the update
                } else {
                    break; // Update succeeded
                }
            }
        }

        // Handle the update on the source chain
        for i in 0..MAX_ITER {
            if self
                .src_chain()
                .proven_client_consensus(self.src_client_id(), dst_chain_height, Height::zero())
                .is_err()
            {
                let src_update = self.build_update_client_on_src(dst_chain_height)?;
                info!(
                    "sending {:?} messages to {}, update client at height {:?}",
                    src_update.len(),
                    self.src_chain.id(),
                    dst_chain_height,
                );

                let src_tx_events = self.src_chain.send_msgs(src_update)?;
                info!("result {:?}\n", src_tx_events);

                let src_err_ev = src_tx_events
                    .into_iter()
                    .find(|event| matches!(event, IbcEvent::ChainError(_)));

                if let Some(err_ev) = src_err_ev {
                    if i == (MAX_ITER - 1) {
                        return Err(LinkError::ClientError(ForeignClientError::ClientUpdate(
                            format!(
                                "Failed to update client on source {} with err: {:?}",
                                self.src_chain.id(),
                                err_ev
                            ),
                        )));
                    } // Else: retry the update
                } else {
                    break; // Update succeeded
                }
            }
        }

        Ok(())
    }

    pub fn send_update_client_and_msgs(
        &mut self,
        dst_update_height: Height,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), LinkError> {
        let mut src_tx_events = vec![];
        let mut dst_tx_events = vec![];

        if self.all_events.is_empty() {
            return Ok((dst_tx_events, src_tx_events));
        }

        let src_update_height = self.all_events[0].height().increment();

        // Clear all_events and collect the src and dst input events if Tx-es fail
        self.all_events = vec![];

        if !self.packet_msgs.is_empty() {
            let mut msgs_to_send = vec![];

            // Check if a consensus state at update_height exists on destination chain already
            if self
                .dst_chain()
                .proven_client_consensus(self.dst_client_id(), src_update_height, Height::zero())
                .is_err()
            {
                msgs_to_send = self.build_update_client_on_dst(src_update_height)?;
                info!("sending update client at height {:?}", src_update_height);
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
            let mut msgs_to_send = self.build_update_client_on_src(dst_update_height)?;
            msgs_to_send.append(&mut self.timeout_msgs);
            info!(
                "sending {:?} messages to {}, update client at height {:?}",
                msgs_to_send.len(),
                self.src_chain.id(),
                dst_update_height,
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

    /// Returns the height (of the source chain) where the chain has outstanding packets.
    fn target_height_and_send_packet_events(&mut self) -> Result<Height, LinkError> {
        // Query packet commitments on source chain that have not been acknowledged
        let pc_request = QueryPacketCommitmentsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: self.src_channel_id().to_string(),
            pagination: None,
        };
        let (packet_commitments, query_height) =
            self.src_chain.query_packet_commitments(pc_request)?;
        if packet_commitments.is_empty() {
            return Ok(query_height);
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
            return Ok(query_height);
        }

        self.all_events = self.src_chain.query_txs(QueryPacketEventDataRequest {
            event_id: IbcEventType::SendPacket,
            source_port_id: self.src_port_id().clone(),
            source_channel_id: self.src_channel_id().clone(),
            destination_port_id: self.dst_port_id().clone(),
            destination_channel_id: self.dst_channel_id().clone(),
            sequences,
            height: query_height,
        })?;

        let mut packet_sequences = vec![];
        for event in self.all_events.iter() {
            let send_event = downcast!(event => IbcEvent::SendPacket)
                .ok_or_else(|| LinkError::Failed("unexpected query tx response".into()))?;
            packet_sequences.push(send_event.packet.sequence);
        }
        info!("received from query_txs {:?}", packet_sequences);

        Ok(query_height)
    }

    fn target_height_and_write_ack_events(&mut self) -> Result<Height, LinkError> {
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
            return Ok(query_height);
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
            return Ok(query_height);
        }

        self.all_events = self
            .src_chain
            .query_txs(QueryPacketEventDataRequest {
                event_id: IbcEventType::WriteAck,
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
            let write_ack_event = downcast!(event => IbcEvent::WriteAcknowledgement)
                .ok_or_else(|| LinkError::Failed("unexpected query tx response".into()))?;
            packet_sequences.push(write_ack_event.packet.sequence);
        }
        info!("received from query_txs {:?}", packet_sequences);

        Ok(query_height)
    }

    /// Handles the relaying of RecvPacket and Timeout messages.
    pub fn relay_recv_packet_and_timeout_msgs(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        // Get the events for the send packets on source chain that have not been received on
        // destination chain (i.e. ack was not seen on source chain).
        // Note: This method call populates `self.all_events`.
        let src_height = self.target_height_and_send_packet_events()?;

        // Skip: no relevant events found.
        if self.all_events.is_empty() {
            return Ok(vec![]);
        }

        for event in self.all_events.iter_mut() {
            event.set_height(src_height);
        }
        let dst_height = self.dst_latest_height()?;

        let (mut dst_res, mut src_res) = if self.channel.connection_delay.as_nanos() > 0 {
            // Update clients & schedule the original events
            self.update_clients(src_height, dst_height)?;
            self.schedule_batch(self.all_events.clone(), dst_height);

            // Block waiting for the delay to pass
            let batch = self.fetch_scheduled_batch()?;

            self.reset_buffers();

            for e in batch.events {
                self.handle_packet_event(&e, batch.dst_height)?;
            }

            // Send messages
            self.send_msgs()?
        } else {
            // Send a multi message transaction with both client update and the packet messages
            for event in self.all_events.clone() {
                self.handle_packet_event(&event, dst_height)?;
            }
            self.send_update_client_and_msgs(dst_height)?
        };

        dst_res.append(&mut src_res);
        Ok(dst_res)
    }

    pub fn relay_packet_ack_msgs(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        // Get the sequences of packets that have been acknowledged on destination chain but still
        // have commitments on source chain (i.e. ack was not seen on source chain)
        let src_height = self.target_height_and_write_ack_events()?;

        // Skip: no relevant events found.
        if self.all_events.is_empty() {
            return Ok(vec![]);
        }

        for event in self.all_events.iter_mut() {
            event.set_height(src_height);
        }
        let dst_height = self.dst_latest_height()?;

        let (mut dst_res, mut src_res) = if self.channel.connection_delay.as_nanos() > 0 {
            // Update clients & schedule the original events
            self.update_clients(src_height, dst_height)?;
            self.schedule_batch(self.all_events.clone(), dst_height);

            // Block waiting for the delay to pass
            let batch = self.fetch_scheduled_batch()?;

            self.reset_buffers();

            for e in batch.events {
                self.handle_packet_event(&e, batch.dst_height)?;
            }

            // Send messages
            self.send_msgs()?
        } else {
            // Send a multi message transaction with both client update and the ACK messages
            for event in self.all_events.clone() {
                self.handle_packet_event(&event, dst_height)?;
            }
            self.send_update_client_and_msgs(dst_height)?
        };

        dst_res.append(&mut src_res);
        Ok(dst_res)
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
        dst_chain_height: Height,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        let packet = event.packet.clone();

        if self
            .dst_channel(dst_chain_height)?
            .state_matches(&ChannelState::Closed)
        {
            Ok((
                None,
                Some(self.build_timeout_on_close_packet(&event.packet, dst_chain_height)?),
            ))
        } else if packet.timeout_height != Height::zero()
            && packet.timeout_height < dst_chain_height
        {
            Ok((
                None,
                Some(self.build_timeout_packet(&event.packet, dst_chain_height)?),
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

    /// Registers a new batch of events to be processed later. The batch can be retrieved once a
    /// predefined delay period elapses, via method `next_scheduled_batch`.
    fn schedule_batch(&mut self, events: Vec<IbcEvent>, dst_height: Height) {
        if events.is_empty() {
            panic!("Cannot schedule an empty event batch")
        }
        info!("Scheduling batch with {} events", events.len());

        let sc_event = ScheduledBatch {
            update_time: Instant::now(),
            events,
            dst_height,
        };
        self.scheduled.push(sc_event);
    }

    /// Pulls out the next batch of events that have fulfilled the predefined delay period and can
    /// now be processed. Blocking call: waits until the delay period for the oldest event batch
    /// is fulfilled. If no batch is currently scheduled, returns immediately with error.
    pub fn fetch_scheduled_batch(&mut self) -> Result<ScheduledBatch, LinkError> {
        if let Some(batch) = self.scheduled.first() {
            info!(
                "Found a scheduled batch with {} events. Waiting for delay period of {:#?}. Elapsed: {:#?}.",
                batch.events.len(), self.channel.connection_delay, batch.update_time.elapsed()
            );
            // Wait until the delay period passes
            while batch.update_time.elapsed() <= self.channel.connection_delay {
                thread::sleep(Duration::from_millis(100))
            }

            let events_batch = self.scheduled.remove(0);
            Ok(events_batch)
        } else {
            Err(LinkError::Failed(
                "There is no scheduled batch of events!".into(),
            ))
        }
    }

    /// Pulls out the next batch of events that have fulfilled the predefined delay period and can
    /// now be processed. Does not block: if no batch fulfilled the delay period (or no batch is
    /// scheduled), return immediately with `None`.
    fn try_fetch_scheduled_batch(&mut self) -> Option<ScheduledBatch> {
        // The head of the scheduled vector contains the oldest scheduled batch.
        if let Some(batch) = self.scheduled.first() {
            if batch.update_time.elapsed() > self.channel.connection_delay {
                let events_batch = self.scheduled.remove(0);
                info!(
                    "Found a scheduled batch with {} events",
                    events_batch.events.len()
                );
                return Some(events_batch);
            }
        }
        None
    }
}
