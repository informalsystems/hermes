use std::fmt;
use std::thread;
use std::time::{Duration, Instant};

use prost_types::Any;
use thiserror::Error;
use tracing::{debug, info, warn};

use ibc::ics24_host::identifier::ChainId;
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

    #[error("clearing of old packets failed")]
    OldPacketClearingFailed,
}

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

pub enum OperationalDataTarget {
    Source,
    Destination,
}

impl fmt::Display for OperationalDataTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationalDataTarget::Source => write!(f, "Source"),
            OperationalDataTarget::Destination => write!(f, "Destination"),
        }
    }
}

pub struct OperationalData {
    chain_height: Height,
    events: Vec<IbcEvent>,
    msgs: Vec<Any>,

    target: OperationalDataTarget,
    /// Stores the time when the clients on the target chain has been updated, i.e., when this data
    /// was scheduled. Necessary for packet delays.
    scheduled_time: Instant,
}

impl OperationalData {
    pub fn new(chain_height: Height, target: OperationalDataTarget) -> Self {
        OperationalData {
            chain_height,
            events: vec![],
            msgs: vec![],
            target,
            scheduled_time: Instant::now(),
        }
    }
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

    // Operational data, for targeting both the source and destination chain.
    // These vectors of operational data are ordered decreasingly by their age, with element at
    // position `0` being the oldest.
    // The operational data targeting the source chain comprises mostly timeout packet messages.
    src_operational_data: Vec<OperationalData>,
    // The operational data targeting the destination chain comprises mostly RecvPacket and Ack msgs.
    dst_operational_data: Vec<OperationalData>,
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
            src_operational_data: Default::default(),
            dst_operational_data: Default::default(),
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

    /// Equivalent to `handle_packet_event` but for the case when packets have non-zero delay.
    fn handle_delayed_packet_event(
        &mut self,
        event: &IbcEvent,
        dst_chain_height: Height,
    ) -> Result<(), LinkError> {
        let (dst_msg, src_msg) = match event {
            IbcEvent::CloseInitChannel(close_init_ev) => {
                info!(
                    "[with delay] {} => event {}",
                    self.src_chain.id(),
                    close_init_ev
                );
                (
                    Some(self.build_chan_close_confirm_from_event(&event)?),
                    None,
                )
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
                        "[with delay] {} => event {} closes the channel",
                        self.src_chain.id(),
                        timeout_ev
                    );
                    (
                        Some(self.build_chan_close_confirm_from_event(&event)?),
                        None,
                    )
                } else {
                    (None, None)
                }
            }
            IbcEvent::SendPacket(send_packet_ev) => {
                info!(
                    "[with delay] {} => event {}",
                    self.src_chain.id(),
                    send_packet_ev
                );
                self.handle_delayed_send_packet_event(&send_packet_ev, dst_chain_height)?
            }
            IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                info!(
                    "[with delay] {} => event {}",
                    self.src_chain.id(),
                    write_ack_ev
                );
                (Some(self.build_ack_from_recv_event(&write_ack_ev)?), None)
            }
            _ => (None, None),
        };

        // Collect messages to be sent to the destination chain
        if let Some(msg) = dst_msg {
            self.packet_msgs.push(msg);
            self.dst_msgs_input_events.push(event.clone());
        }

        // Collect timeout messages, to be sent to the source chain
        if let Some(msg) = src_msg {
            // For Ordered channels a single timeout event should be sent as this closes the channel.
            // Otherwise a multi message transaction will fail.
            if self.unordered_channel() || self.timeout_msgs.is_empty() {
                self.timeout_msgs.push(msg);
                self.src_msgs_input_events.push(event.clone());
            }
        }

        Ok(())
    }

    fn handle_send_packet_event_unified(
        &self,
        _event: &SendPacket,
        _dst_chain_height: Height,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        unimplemented!()
    }

    fn handle_delayed_send_packet_event(
        &mut self,
        event: &SendPacket,
        dst_chain_height: Height,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        let packet = event.packet.clone();

        // The latest height of the destination chain.
        // Necessary for computing timeout heights correctly.
        let latest_dst_chain_height = self.dst_latest_height()?;

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
            warn!(
                "Building timeout packet with proofs for height {}",
                dst_chain_height
            );
            // Handle timeouts
            // The packet timed-out relative to the "old" destination chain height. The "old" height
            // is the height which the dst. chain had when this batch of events was scheduled.
            // In this case, relay to the source chain the timeout message.
            Ok((
                None,
                Some(self.build_timeout_packet(&event.packet, dst_chain_height)?),
            ))
        } else if packet.timeout_height != Height::zero()
            && packet.timeout_height < latest_dst_chain_height
        {
            warn!(
                "Prepping timeout packet with proofs for height {}",
                latest_dst_chain_height
            );
            // The packet timed-out relative to the latest destination chain height.
            // We build an updateClient message for the client hosted on the source chain, and
            // schedule this event in a separate batch for later processing.
            self.schedule_batch(
                vec![IbcEvent::SendPacket(event.clone())],
                latest_dst_chain_height.decrement().unwrap(),
            );
            Ok((
                None,
                self.build_update_client_on_src(dst_chain_height)?.pop(),
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

    // Determines if the events received are relevant and should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn filter_events(&mut self, events: &[IbcEvent]) -> Vec<IbcEvent> {
        let mut result = vec![];

        for event in events.iter() {
            match event {
                IbcEvent::SendPacket(send_packet_ev) => {
                    if self.src_channel_id() == &send_packet_ev.packet.source_channel
                        && self.src_port_id() == &send_packet_ev.packet.source_port
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                    if self.channel.src_channel_id() == &write_ack_ev.packet.destination_channel
                        && self.channel.src_port_id() == &write_ack_ev.packet.destination_port
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::CloseInitChannel(chan_close_ev) => {
                    if self.channel.src_channel_id() == chan_close_ev.channel_id()
                        && self.channel.src_port_id() == chan_close_ev.port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::TimeoutPacket(timeout_ev) => {
                    if self.channel.src_channel_id() == timeout_ev.src_channel_id()
                        && self.channel.src_port_id() == timeout_ev.src_port_id()
                    {
                        result.push(event.clone());
                    }
                }
                _ => {}
            }
        }
        result
    }

    // May adjust the height of the input vector of events.
    // Checks if the client on destination chain is at a higher height than the events height.
    // This can happen if a client update has happened after the event was emitted but before
    // this point when the relayer starts to process the events.
    fn adjust_events_height(&self, events: &mut Vec<IbcEvent>) -> Result<(), LinkError> {
        let event_height = match events.get(0) {
            None => return Ok(()),
            Some(ev) => ev.height(),
        };

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

        // (event_height + 1) is the height at which the client on destination chain
        // should be updated, unless ...
        if trusted_height > event_height.increment() {
            // ... client is already at a higher height.
            let new_height = trusted_height
                .decrement()
                .map_err(|e| LinkError::Failed(e.to_string()))?;
            events.iter_mut().for_each(|ev| ev.set_height(new_height));
        }

        Ok(())
    }

    fn reset_buffers(&mut self) {
        self.dst_msgs_input_events = vec![];
        self.src_msgs_input_events = vec![];
        self.packet_msgs = vec![];
        self.timeout_msgs = vec![];
    }

    fn relay_pending_packets(&mut self, height: Height) -> Result<(), LinkError> {
        info!(
            "clearing old packets on path {} -> {}",
            self.src_chain.id(),
            self.dst_chain.id()
        );
        for _i in 0..MAX_ITER {
            if self
                .relay_recv_packet_and_timeout_msgs(Some(height))
                .is_ok()
                && self.relay_packet_ack_msgs(Some(height)).is_ok()
            {
                return Ok(());
            }
            self.reset_buffers();
            self.all_events = vec![];
        }
        Err(LinkError::OldPacketClearingFailed)
    }

    /// Should not run more than once per execution.
    pub fn clear_packets(&mut self, height: Height) -> Result<(), LinkError> {
        if self.clear_packets {
            self.relay_pending_packets(height)?;
            info!("Finished clearing pending packets");
            self.clear_packets = false;
        }

        Ok(())
    }

    /// Iterate through the IBC Events, build the message for each and collect all at same height.
    pub fn relay_from_events(&mut self, batch: EventBatch) -> Result<(), LinkError> {
        self.clear_packets(batch.height)?;

        // Collect relevant events & adjust their height.
        let mut events = self.filter_events(&batch.events);
        self.adjust_events_height(&mut events)?;

        // Obtain the operational data for the source chain (mostly timeout packets) and for the
        // destination chain (receive packet messages).
        let (src_opt, dst_opt) = self.generate_operational_data(events)?;

        if let Some(src_od) = src_opt {
            self.schedule_operational_data(src_od)?;
        }
        if let Some(dst_od) = dst_opt {
            self.schedule_operational_data(dst_od)?;
        }

        Ok(())
    }

    fn generate_operational_data(
        &self,
        input: Vec<IbcEvent>,
    ) -> Result<(Option<OperationalData>, Option<OperationalData>), LinkError> {
        let src_height = match input.get(0) {
            None => return Ok((None, None)),
            Some(ev) => ev.height(),
        };

        let mut src_od = OperationalData::new(src_height, OperationalDataTarget::Source);
        let mut dst_od = OperationalData::new(
            self.dst_latest_height()?,
            OperationalDataTarget::Destination,
        );

        for event in input {
            let (dst_msg, src_msg) = match event {
                IbcEvent::CloseInitChannel(ref close_init_ev) => {
                    info!(
                        "[generating OD] {} => event {}",
                        self.src_chain.id(),
                        close_init_ev
                    );
                    (
                        Some(self.build_chan_close_confirm_from_event(&event)?),
                        None,
                    )
                }
                IbcEvent::TimeoutPacket(ref timeout_ev) => {
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
                            "[generating OD] {} => event {} closes the channel",
                            self.src_chain.id(),
                            timeout_ev
                        );
                        (
                            Some(self.build_chan_close_confirm_from_event(&event)?),
                            None,
                        )
                    } else {
                        (None, None)
                    }
                }
                IbcEvent::SendPacket(ref send_packet_ev) => {
                    info!(
                        "[generating OD] {} => event {}",
                        self.src_chain.id(),
                        send_packet_ev
                    );
                    self.handle_send_packet_event_unified(&send_packet_ev, dst_od.chain_height)?
                }
                IbcEvent::WriteAcknowledgement(ref write_ack_ev) => {
                    info!(
                        "[generating OD] {} => event {}",
                        self.src_chain.id(),
                        write_ack_ev
                    );
                    (Some(self.build_ack_from_recv_event(&write_ack_ev)?), None)
                }
                _ => (None, None),
            };

            // Collect messages to be sent to the destination chain
            if let Some(msg) = dst_msg {
                dst_od.msgs.push(msg);
                dst_od.events.push(event.clone());
            }

            // Collect timeout messages, to be sent to the source chain
            if let Some(msg) = src_msg {
                // For Ordered channels a single timeout event should be sent as this closes the channel.
                // Otherwise a multi message transaction will fail.
                if self.unordered_channel() || src_od.msgs.is_empty() {
                    src_od.msgs.push(msg);
                    src_od.events.push(event.clone());
                }
            }
        }

        Ok((Some(src_od), Some(dst_od)))
    }

    fn apply(&mut self, od: OperationalData) -> Result<(), LinkError> {
        for i in 0..MAX_ITER {
            info!(
                "Relaying with operational data to {} with {} msgs [{}/{}]",
                od.target,
                od.msgs.len(),
                i,
                MAX_ITER
            );

            // Send messages
            let res = self.send_msgs()?;
            debug!("\nresult {:?}", res);

            if self.all_events.is_empty() {
                break;
            }

            debug!("retrying");
        }

        self.all_events = vec![];
        Ok(())
    }

    /// Send a multi message transaction with packet messages, prepending the client update.
    /// Ignores any delay period for packets.
    #[allow(dead_code)]
    fn relay_immediately(&mut self) -> Result<(), LinkError> {
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

    /// Handles updating the client on the destination chain
    fn update_client_dst(&self, src_chain_height: Height) -> Result<(), LinkError> {
        // Handle the update on the destination chain
        // Check if a consensus state at update_height exists on destination chain already
        for i in 0..MAX_ITER {
            if self
                .dst_chain()
                .proven_client_consensus(self.dst_client_id(), src_chain_height, Height::zero())
                .is_err()
            {
                let dst_update = self.build_update_client_on_dst(src_chain_height)?;
                info!(
                    "sending updateClient to client hosted on dest. chain {} for height {:?}",
                    self.dst_chain().id(),
                    src_chain_height
                );

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

        Ok(())
    }

    /// Handles updating the client on the source chain
    fn update_client_src(&self, dst_chain_height: Height) -> Result<(), LinkError> {
        for i in 0..MAX_ITER {
            if self
                .src_chain()
                .proven_client_consensus(self.src_client_id(), dst_chain_height, Height::zero())
                .is_err()
            {
                let src_update = self.build_update_client_on_src(dst_chain_height)?;
                info!(
                    "sending updateClient to client hosted on src. chain {} for height {:?}",
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

    /// Sends ClientUpdate transactions ahead of a scheduled batch.
    /// Includes basic retrying and returns failure only after all retries are exhausted.
    pub fn update_clients(
        &self,
        src_chain_height: Height,
        dst_chain_height: Height,
    ) -> Result<(), LinkError> {
        self.update_client_dst(src_chain_height)?;
        self.update_client_src(dst_chain_height)
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

    /// Populates the `self.all_events` field with relevant packet events for building RecvPacket
    /// and timeout messages. Returns the height (on source chain) corresponding to these events.
    fn target_height_and_send_packet_events(
        &mut self,
        opt_query_height: Option<Height>,
    ) -> Result<Height, LinkError> {
        // Query packet commitments on source chain that have not been acknowledged
        let pc_request = QueryPacketCommitmentsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: self.src_channel_id().to_string(),
            pagination: None,
        };
        let (packet_commitments, src_response_height) =
            self.src_chain.query_packet_commitments(pc_request)?;
        if packet_commitments.is_empty() {
            return Ok(src_response_height);
        }
        let commit_sequences = packet_commitments.iter().map(|p| p.sequence).collect();
        info!(
            "packets that still have commitments on {}: {:?}",
            self.src_chain.id(),
            commit_sequences
        );

        let query_height = opt_query_height.unwrap_or(src_response_height);

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
            "recv packets to send out to {} of the ones with commitments on source {}: {:?}",
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

    /// Populates the `self.all_events` field with relevant packet events for building ack
    /// messages. Returns the height (on source chain) corresponding to these events.
    fn target_height_and_write_ack_events(
        &mut self,
        opt_query_height: Option<Height>,
    ) -> Result<Height, LinkError> {
        // Get the sequences of packets that have been acknowledged on source
        let pc_request = QueryPacketAcknowledgementsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: self.src_channel_id().to_string(),
            pagination: None,
        };
        let (acks_on_source, src_response_height) = self
            .src_chain
            .query_packet_acknowledgements(pc_request)
            .map_err(|e| LinkError::QueryError(self.src_chain.id(), e))?;

        if acks_on_source.is_empty() {
            return Ok(src_response_height);
        }

        let query_height = opt_query_height.unwrap_or(src_response_height);

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
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn relay_recv_packet_and_timeout_msgs(
        &mut self,
        opt_query_height: Option<Height>,
    ) -> Result<Vec<IbcEvent>, LinkError> {
        // Get the events for the send packets on source chain that have not been received on
        // destination chain (i.e. ack was not seen on source chain).
        // Note: This method call populates `self.all_events`.
        let src_height = self.target_height_and_send_packet_events(opt_query_height)?;

        // Skip: no relevant events found.
        if self.all_events.is_empty() {
            return Ok(vec![]);
        }

        for event in self.all_events.iter_mut() {
            event.set_height(src_height);
        }

        let dst_update_height = self.dst_latest_height()?;

        let (mut dst_res, mut src_res) = if self.channel.connection_delay.as_nanos() > 0 {
            // Update clients & schedule the original events
            let src_update_height = src_height.increment();
            self.update_clients(src_update_height, dst_update_height)?;
            self.schedule_batch(
                self.all_events.clone(),
                dst_update_height.decrement().unwrap(),
            );

            // Block waiting for the delay to pass
            let batch = self.fetch_scheduled_batch()?;

            self.reset_buffers();

            for e in batch.events {
                info!("Handling event @ height {}", e.height());
                self.handle_delayed_packet_event(&e, batch.dst_height)?;
            }

            // Send messages
            self.send_msgs()?
        } else {
            // Send a multi message transaction with both client update and the packet messages
            for event in self.all_events.clone() {
                self.handle_packet_event(&event, dst_update_height)?;
            }
            self.send_update_client_and_msgs(dst_update_height)?
        };

        dst_res.append(&mut src_res);
        Ok(dst_res)
    }

    /// Handles the relaying of packet acknowledgment messages.
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn relay_packet_ack_msgs(
        &mut self,
        opt_query_height: Option<Height>,
    ) -> Result<Vec<IbcEvent>, LinkError> {
        self.all_events = vec![];
        // Get the sequences of packets that have been acknowledged on destination chain but still
        // have commitments on source chain (i.e. ack was not seen on source chain)
        let src_height = self.target_height_and_write_ack_events(opt_query_height)?;

        // Skip: no relevant events found.
        if self.all_events.is_empty() {
            return Ok(vec![]);
        }

        for event in self.all_events.iter_mut() {
            event.set_height(src_height);
        }

        let dst_update_height = self.dst_latest_height()?;

        let (mut dst_res, mut src_res) = if self.channel.connection_delay.as_nanos() > 0 {
            // Update clients & schedule the original events
            let src_update_height = src_height.increment();
            self.update_clients(src_update_height, dst_update_height)?;
            self.schedule_batch(self.all_events.clone(), dst_update_height);

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
                self.handle_packet_event(&event, dst_update_height)?;
            }
            self.send_update_client_and_msgs(dst_update_height)?
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
            && packet.timeout_height < self.dst_latest_height()?
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
        info!(
            "Scheduling batch with {} events for dst height: {}",
            events.len(),
            dst_height
        );

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
                "Found a scheduled batch with {} events. Waiting for delay period ({:#?}) to pass",
                batch.events.len(),
                self.channel.connection_delay
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

    fn schedule_operational_data(&mut self, mut od: OperationalData) -> Result<(), LinkError> {
        if od.msgs.is_empty() {
            panic!("Cannot schedule an empty operational data!")
        }
        info!(
            "Scheduling op. data with {} events for dst chain height: {}",
            od.events.len(),
            od.chain_height
        );

        od.scheduled_time = Instant::now();

        // Update clients ahead of scheduling the operational data, if the delays are non-zero.
        if self.channel.connection_delay.as_nanos() > 0 {
            let target_height = od.chain_height.increment();
            match od.target {
                OperationalDataTarget::Source => self.update_client_src(target_height)?,
                OperationalDataTarget::Destination => self.update_client_dst(target_height)?,
            };
        }

        match od.target {
            OperationalDataTarget::Source => self.src_operational_data.push(od),
            OperationalDataTarget::Destination => self.dst_operational_data.push(od),
        };

        Ok(())
    }

    /// Pulls out the next operational data that has fulfilled the predefined delay period and can
    /// now be processed. Does not block: if no OD fulfilled the delay period (or none is
    /// scheduled), returns immediately with `None`.
    fn try_fetch_scheduled_operational_data(&mut self) -> Option<OperationalData> {
        // The head of the op. data vector contains the oldest entry.
        if let Some(od_data_src) = self.src_operational_data.first() {
            if od_data_src.scheduled_time.elapsed() > self.channel.connection_delay {
                let op_src = self.src_operational_data.remove(0);
                info!(
                    "Found operational data for source with {} events (delayed by: {:#?})",
                    op_src.events.len(),
                    op_src.scheduled_time.elapsed()
                );
                return Some(op_src);
            }
        }

        // No operational data was found targeting the source chain; try for the destination chain.
        if let Some(od_data_dst) = self.dst_operational_data.first() {
            if od_data_dst.scheduled_time.elapsed() > self.channel.connection_delay {
                let op_dst = self.dst_operational_data.remove(0);
                info!(
                    "Found operational data for destination with {} events (delayed by: {:#?})",
                    op_dst.events.len(),
                    op_dst.scheduled_time.elapsed()
                );
                return Some(op_dst);
            }
        }
        None
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
        info!(
            "relaying packets on path {} <-> {}",
            self.a_to_b.src_chain().id(),
            self.a_to_b.dst_chain().id()
        );

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

            if let Some(od) = self.a_to_b.try_fetch_scheduled_operational_data() {
                self.a_to_b.apply(od)?;
            }

            if let Ok(batch) = events_b.try_recv() {
                self.b_to_a.relay_from_events(batch.unwrap_or_clone())?;
            }

            if let Some(od) = self.b_to_a.try_fetch_scheduled_operational_data() {
                self.b_to_a.apply(od)?;
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
            connection_delay: Duration::from_nanos(a_connection.delay_period()),
        };

        Ok(Link::new(channel))
    }

    pub fn build_and_send_recv_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        self.a_to_b.relay_recv_packet_and_timeout_msgs(None)
    }

    pub fn build_and_send_ack_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        self.a_to_b.relay_packet_ack_msgs(None)
    }
}
