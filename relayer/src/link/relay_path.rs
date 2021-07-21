use std::collections::HashMap;
use std::time::Instant;
use std::{fmt, thread};

use itertools::Itertools;
use prost_types::Any;
use tracing::{debug, error, info, trace};

use ibc::{
    downcast,
    events::{IbcEvent, IbcEventType, PrettyEvents},
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
    query::QueryTxRequest,
    signer::Signer,
    timestamp::ZERO_DURATION,
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
use crate::link::operational_data::{OperationalData, OperationalDataTarget, TransitMessage};
use crate::link::relay_summary::RelaySummary;

const MAX_RETRIES: usize = 5;

pub struct RelayPath {
    channel: Channel,
    // Marks whether this path has already cleared pending packets.
    // Packets should be cleared once (at startup), then this
    // flag turns to `false`.
    clear_packets: bool,
    // Operational data, targeting both the source and destination chain.
    // These vectors of operational data are ordered decreasingly by their age, with element at
    // position `0` being the oldest.
    // The operational data targeting the source chain comprises mostly timeout packet messages.
    src_operational_data: Vec<OperationalData>,
    // The operational data targeting the destination chain comprises mostly RecvPacket and Ack msgs.
    dst_operational_data: Vec<OperationalData>,
}

impl RelayPath {
    pub fn new(channel: Channel) -> Self {
        Self {
            channel,
            clear_packets: true,
            src_operational_data: vec![],
            dst_operational_data: vec![],
        }
    }

    #[allow(clippy::borrowed_box)]
    pub fn src_chain(&self) -> &Box<dyn ChainHandle> {
        self.channel.src_chain()
    }

    #[allow(clippy::borrowed_box)]
    pub fn dst_chain(&self) -> &Box<dyn ChainHandle> {
        self.channel.dst_chain()
    }

    pub fn src_client_id(&self) -> &ClientId {
        self.channel.src_client_id()
    }

    pub fn dst_client_id(&self) -> &ClientId {
        self.channel.dst_client_id()
    }

    pub fn src_connection_id(&self) -> &ConnectionId {
        self.channel.src_connection_id()
    }

    pub fn dst_connection_id(&self) -> &ConnectionId {
        self.channel.dst_connection_id()
    }

    pub fn src_port_id(&self) -> &PortId {
        self.channel.src_port_id()
    }

    pub fn dst_port_id(&self) -> &PortId {
        self.channel.dst_port_id()
    }

    pub fn src_channel_id(&self) -> Result<&ChannelId, LinkError> {
        self.channel.src_channel_id().ok_or_else(|| {
            LinkError::Failed(format!(
                "channel_id on source chain '{}' is 'None'",
                self.src_chain().id()
            ))
        })
    }

    pub fn dst_channel_id(&self) -> Result<&ChannelId, LinkError> {
        self.channel.dst_channel_id().ok_or_else(|| {
            LinkError::Failed(format!(
                "channel_id on destination chain '{}' is 'None'",
                self.dst_chain().id()
            ))
        })
    }

    pub fn channel(&self) -> &Channel {
        &self.channel
    }

    fn src_channel(&self, height: Height) -> Result<ChannelEnd, LinkError> {
        Ok(self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id()?, height)
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?)
    }

    fn dst_channel(&self, height: Height) -> Result<ChannelEnd, LinkError> {
        Ok(self
            .dst_chain()
            .query_channel(self.dst_port_id(), self.dst_channel_id()?, height)
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?)
    }

    fn src_signer(&self) -> Result<Signer, LinkError> {
        self.src_chain().get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from src chain {} with error: {}",
                self.src_chain().id(),
                e
            ))
        })
    }

    fn dst_signer(&self) -> Result<Signer, LinkError> {
        self.dst_chain().get_signer().map_err(|e| {
            LinkError::Failed(format!(
                "could not retrieve signer from dst chain {} with error: {}",
                self.dst_chain().id(),
                e
            ))
        })
    }

    pub fn dst_latest_height(&self) -> Result<Height, LinkError> {
        self.dst_chain()
            .query_latest_height()
            .map_err(|e| LinkError::QueryError(self.dst_chain().id(), e))
    }

    fn unordered_channel(&self) -> bool {
        self.channel.ordering == Order::Unordered
    }

    fn ordered_channel(&self) -> bool {
        self.channel.ordering == Order::Ordered
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, LinkError> {
        let client = self.restore_dst_client();
        client
            .build_update_client(height)
            .map_err(LinkError::ClientError)
    }

    pub fn build_update_client_on_src(&self, height: Height) -> Result<Vec<Any>, LinkError> {
        let client = self.restore_src_client();
        client
            .build_update_client(height)
            .map_err(LinkError::ClientError)
    }

    fn build_chan_close_confirm_from_event(&self, event: &IbcEvent) -> Result<Any, LinkError> {
        let src_channel_id = self.src_channel_id()?;
        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, event.height())
            .map_err(|e| ChannelError::Failed(format!("failed to build channel proofs: {}", e)))?;

        // Build the domain type message
        let new_msg = MsgChannelCloseConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: src_channel_id.clone(),
            proofs,
            signer: self.dst_signer()?,
        };

        Ok(new_msg.to_any())
    }

    // Determines if the events received are relevant and should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn filter_events(&self, events: &[IbcEvent]) -> Vec<IbcEvent> {
        let mut result = vec![];

        let src_channel_id = if let Ok(some_id) = self.src_channel_id() {
            some_id
        } else {
            return vec![];
        };

        for event in events.iter() {
            match event {
                IbcEvent::SendPacket(send_packet_ev) => {
                    if src_channel_id == send_packet_ev.src_channel_id()
                        && self.src_port_id() == send_packet_ev.src_port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                    if src_channel_id == write_ack_ev.dst_channel_id()
                        && self.src_port_id() == write_ack_ev.dst_port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::CloseInitChannel(chan_close_ev) => {
                    if src_channel_id == chan_close_ev.channel_id()
                        && self.src_port_id() == chan_close_ev.port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::TimeoutPacket(timeout_ev) => {
                    if src_channel_id == timeout_ev.src_channel_id()
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

    fn relay_pending_packets(&mut self, height: Height) -> Result<(), LinkError> {
        for _ in 0..MAX_RETRIES {
            if self
                .build_recv_packet_and_timeout_msgs(Some(height))
                .is_ok()
                && self.build_packet_ack_msgs(Some(height)).is_ok()
            {
                return Ok(());
            }
        }
        Err(LinkError::OldPacketClearingFailed)
    }

    /// Clears any packets that were sent before `height`, either if the `clear_packets` flag
    /// is set or if clearing is forced by the caller.
    pub fn schedule_packet_clearing(
        &mut self,
        height: Height,
        force: bool,
    ) -> Result<(), LinkError> {
        if self.clear_packets || force {
            // Disable further clearing of old packets by default.
            // Clearing may still happen: upon new blocks, when `force = true`.
            self.clear_packets = false;

            info!(
                "[{}] clearing pending packets from events before height {}",
                self, height
            );

            let clear_height = height.decrement().map_err(|e| {
                LinkError::Failed(format!(
                    "Cannot clear packets @height {}, because this height cannot be decremented: {}",
                    height,
                    e.to_string()
                ))
            })?;

            self.relay_pending_packets(clear_height)?;

            info!(
                "[{}] finished scheduling the clearing of pending packets",
                self
            );
        }

        Ok(())
    }

    /// Generate & schedule operational data from the input `batch` of IBC events.
    pub fn update_schedule(&mut self, batch: EventBatch) -> Result<(), LinkError> {
        // Collect relevant events from the incoming batch & adjust their height.
        let events = self.filter_events(&batch.events);

        // Transform the events into operational data items
        self.events_to_operational_data(events)
    }

    /// Produces and schedules operational data for this relaying path based on the input events.
    fn events_to_operational_data(&mut self, events: Vec<IbcEvent>) -> Result<(), LinkError> {
        // Obtain the operational data for the source chain (mostly timeout packets) and for the
        // destination chain (e.g., receive packet messages).
        let (src_opt, dst_opt) = self.generate_operational_data(events)?;

        if let Some(src_od) = src_opt {
            self.schedule_operational_data(src_od)?;
        }
        if let Some(dst_od) = dst_opt {
            self.schedule_operational_data(dst_od)?;
        }

        Ok(())
    }

    /// Generates operational data out of a set of events.
    /// Handles building operational data targeting both the destination and source chains.
    ///
    /// For the destination chain, the op. data will contain `RecvPacket` messages,
    /// as well as channel close handshake (`ChanCloseConfirm`), `WriteAck` messages.
    ///
    /// For the source chain, the op. data will contain timeout packet messages (`MsgTimeoutOnClose`
    /// or `MsgTimeout`).
    fn generate_operational_data(
        &self,
        input: Vec<IbcEvent>,
    ) -> Result<(Option<OperationalData>, Option<OperationalData>), LinkError> {
        if !input.is_empty() {
            info!(
                "[{}] generate messages from batch with {} events",
                self,
                input.len()
            );
        }
        let src_height = match input.get(0) {
            None => return Ok((None, None)),
            Some(ev) => ev.height(),
        };

        let dst_height = self.dst_latest_height()?;
        // Operational data targeting the source chain (e.g., Timeout packets)
        let mut src_od = OperationalData::new(dst_height, OperationalDataTarget::Source);
        // Operational data targeting the destination chain (e.g., SendPacket messages)
        let mut dst_od = OperationalData::new(src_height, OperationalDataTarget::Destination);

        for event in input {
            debug!("[{}] {} => {}", self, self.src_chain().id(), event);
            let (dst_msg, src_msg) = match event {
                IbcEvent::CloseInitChannel(_) => (
                    Some(self.build_chan_close_confirm_from_event(&event)?),
                    None,
                ),
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
                        (
                            Some(self.build_chan_close_confirm_from_event(&event)?),
                            None,
                        )
                    } else {
                        (None, None)
                    }
                }
                IbcEvent::SendPacket(ref send_packet_ev) => {
                    if self.send_packet_event_handled(send_packet_ev)? {
                        debug!("[{}] {} already handled", self, send_packet_ev);
                        (None, None)
                    } else {
                        self.build_recv_or_timeout_from_send_packet_event(
                            send_packet_ev,
                            dst_height,
                        )?
                    }
                }
                IbcEvent::WriteAcknowledgement(ref write_ack_ev) => {
                    if self
                        .dst_channel(Height::zero())?
                        .state_matches(&ChannelState::Closed)
                    {
                        (None, None)
                    } else if self.write_ack_event_handled(write_ack_ev)? {
                        debug!("[{}] {} already handled", self, write_ack_ev);
                        (None, None)
                    } else {
                        (self.build_ack_from_recv_event(write_ack_ev)?, None)
                    }
                }
                _ => (None, None),
            };

            // Collect messages to be sent to the destination chain (e.g., RecvPacket)
            if let Some(msg) = dst_msg {
                debug!(
                    "[{}] {} <= {} from {}",
                    self,
                    self.dst_chain().id(),
                    msg.type_url,
                    event
                );
                dst_od.batch.push(TransitMessage {
                    event: event.clone(),
                    msg,
                });
            }

            // Collect timeout messages, to be sent to the source chain
            if let Some(msg) = src_msg {
                // For Ordered channels a single timeout event should be sent as this closes the channel.
                // Otherwise a multi message transaction will fail.
                if self.unordered_channel() || src_od.batch.is_empty() {
                    debug!(
                        "[{}] {} <= {} from {}",
                        self,
                        self.src_chain().id(),
                        msg.type_url,
                        event
                    );
                    src_od.batch.push(TransitMessage { event, msg });
                }
            }
        }

        let src_od_res = if src_od.batch.is_empty() {
            None
        } else {
            Some(src_od)
        };

        let dst_od_res = if dst_od.batch.is_empty() {
            None
        } else {
            Some(dst_od)
        };

        Ok((src_od_res, dst_od_res))
    }

    /// Returns the events generated by the target chain
    pub(crate) fn relay_from_operational_data(
        &mut self,
        initial_od: OperationalData,
    ) -> Result<RelaySummary, LinkError> {
        // We will operate on potentially different operational data if the initial one fails.
        let mut odata = initial_od;

        for i in 0..MAX_RETRIES {
            info!(
                "[{}] relay op. data of {} msgs(s) to {} (height {}), delayed by: {:?} [try {}/{}]",
                self,
                odata.batch.len(),
                odata.target,
                odata.proofs_height.increment(),
                odata.scheduled_time.elapsed(),
                i + 1,
                MAX_RETRIES
            );

            // Consume the operational data by attempting to send its messages
            match self.send_from_operational_data(odata.clone()) {
                Ok(summary) => {
                    // Done with this op. data
                    info!("[{}] success", self);

                    return Ok(summary);
                }
                Err(LinkError::SendError(ev)) => {
                    // This error means we could retry
                    error!("[{}] error {}", self, ev);
                    if i + 1 == MAX_RETRIES {
                        error!(
                            "[{}] {}/{} retries exhausted. giving up",
                            self,
                            i + 1,
                            MAX_RETRIES
                        )
                    } else {
                        // If we haven't exhausted all retries, regenerate the op. data & retry
                        match self.regenerate_operational_data(odata.clone()) {
                            None => return Ok(RelaySummary::empty()), // Nothing to retry
                            Some(new_od) => odata = new_od,
                        }
                    }
                }
                Err(e) => {
                    // Unrecoverable error, propagate up the stack
                    return Err(e);
                }
            }
        }

        Ok(RelaySummary::empty())
    }

    /// Helper for managing retries of the `relay_from_operational_data` method.
    /// Expects as input the initial operational data that failed to send.
    ///
    /// Return value:
    ///   - `Some(..)`: a new operational data from which to retry sending,
    ///   - `None`: all the events in the initial operational data were exhausted (i.e., turned
    ///   into timeouts), so there is nothing to retry.
    ///
    /// Side effects: may schedule a new operational data targeting the source chain, comprising
    /// new timeout messages.
    fn regenerate_operational_data(
        &mut self,
        initial_odata: OperationalData,
    ) -> Option<OperationalData> {
        info!(
            "[{}] failed. Regenerate operational data from {} events",
            self,
            initial_odata.events().len()
        );

        // Retry by re-generating the operational data using the initial events
        let (src_opt, dst_opt) = match self.generate_operational_data(initial_odata.events()) {
            Ok(new_operational_data) => new_operational_data,
            Err(e) => {
                error!(
                    "[{}] failed to regenerate operational data from initial data: {} \
                    with error {}, discarding this op. data",
                    self, initial_odata, e
                );
                return None;
            } // Cannot retry, contain the error by reporting a None
        };

        if let Some(src_od) = src_opt {
            if src_od.target == initial_odata.target {
                // Our target is the _source_ chain, retry these messages
                info!("[{}] will retry with op data {}", self, src_od);
                return Some(src_od);
            } else {
                // Our target is the _destination_ chain, the data in `src_od` contains
                // potentially new timeout messages that have to be handled separately.
                if let Err(e) = self.schedule_operational_data(src_od) {
                    error!(
                        "[{}] failed to schedule newly-generated operational data from \
                    initial data: {} with error {}, discarding this op. data",
                        self, initial_odata, e
                    );
                    return None;
                }
            }
        }

        if let Some(dst_od) = dst_opt {
            if dst_od.target == initial_odata.target {
                // Our target is the _destination_ chain, retry these messages
                info!("[{}] will retry with op data {}", self, dst_od);
                return Some(dst_od);
            } else {
                // Our target is the _source_ chain, but `dst_od` has new messages
                // intended for the destination chain, this should never be the case
                error!(
                    "[{}] generated new messages for destination chain while handling \
                    failed events targeting the source chain!",
                    self
                );
            }
        } else {
            // There is no message intended for the destination chain
            if initial_odata.target == OperationalDataTarget::Destination {
                info!("[{}] exhausted all events from this operational data", self);
                return None;
            }
        }

        None
    }

    /// Sends a transaction to the chain targeted by the operational data `odata`.
    /// If the transaction generates an error, returns the error as well as  `LinkError::SendError`
    /// if  input events if a sending failure occurs.
    /// Returns the events generated by the target chain upon success.
    fn send_from_operational_data(
        &mut self,
        odata: OperationalData,
    ) -> Result<RelaySummary, LinkError> {
        if odata.batch.is_empty() {
            error!("[{}] ignoring empty operational data!", self);
            return Ok(RelaySummary::empty());
        }

        let target = match odata.target {
            OperationalDataTarget::Source => self.src_chain(),
            OperationalDataTarget::Destination => self.dst_chain(),
        };

        let msgs = odata.assemble_msgs(self)?;

        let tx_events = target.send_msgs(msgs)?;
        info!("[{}] result {}\n", self, PrettyEvents(&tx_events));

        let ev = tx_events
            .clone()
            .into_iter()
            .find(|event| matches!(event, IbcEvent::ChainError(_)));

        match ev {
            Some(ev) => Err(LinkError::SendError(Box::new(ev))),
            None => Ok(RelaySummary::from_events(tx_events)),
        }
    }

    /// Checks if a sent packet has been received on destination.
    fn send_packet_received_on_dst(&self, packet: &Packet) -> Result<bool, LinkError> {
        let unreceived_packet =
            self.dst_chain()
                .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                    port_id: self.dst_port_id().to_string(),
                    channel_id: self.dst_channel_id()?.to_string(),
                    packet_commitment_sequences: vec![packet.sequence.into()],
                })?;

        Ok(unreceived_packet.is_empty())
    }

    /// Checks if a packet commitment has been cleared on source.
    /// The packet commitment is cleared when either an acknowledgment or a timeout is received on source.
    fn send_packet_commitment_cleared_on_src(&self, packet: &Packet) -> Result<bool, LinkError> {
        let (bytes, _) = self.src_chain().build_packet_proofs(
            PacketMsgType::Recv,
            self.src_port_id(),
            self.src_channel_id()?,
            packet.sequence,
            Height::zero(),
        )?;

        Ok(bytes.is_empty())
    }

    /// Checks if a send packet event has already been handled (e.g. by another relayer).
    fn send_packet_event_handled(&self, sp: &SendPacket) -> Result<bool, LinkError> {
        Ok(self.send_packet_received_on_dst(&sp.packet)?
            || self.send_packet_commitment_cleared_on_src(&sp.packet)?)
    }

    /// Checks if an acknowledgement for the given packet has been received on
    /// source chain of the packet, ie. the destination chain of the relay path
    /// that sends the acknowledgment.
    fn recv_packet_acknowledged_on_src(&self, packet: &Packet) -> Result<bool, LinkError> {
        let unreceived_ack =
            self.dst_chain()
                .query_unreceived_acknowledgement(QueryUnreceivedAcksRequest {
                    port_id: self.dst_port_id().to_string(),
                    channel_id: self.dst_channel_id()?.to_string(),
                    packet_ack_sequences: vec![packet.sequence.into()],
                })?;

        Ok(unreceived_ack.is_empty())
    }

    /// Checks if a receive packet event has already been handled (e.g. by another relayer).
    fn write_ack_event_handled(&self, rp: &WriteAcknowledgement) -> Result<bool, LinkError> {
        self.recv_packet_acknowledged_on_src(&rp.packet)
    }

    /// Returns `true` if the delay for this relaying path is zero.
    /// Conversely, returns `false` if the delay is non-zero.
    pub fn zero_delay(&self) -> bool {
        self.channel.connection_delay == ZERO_DURATION
    }

    /// Handles updating the client on the destination chain
    fn update_client_dst(&self, src_chain_height: Height) -> Result<(), LinkError> {
        // Handle the update on the destination chain
        // Check if a consensus state at update_height exists on destination chain already
        if self
            .dst_chain()
            .proven_client_consensus(self.dst_client_id(), src_chain_height, Height::zero())
            .is_ok()
        {
            return Ok(());
        }

        let mut dst_err_ev = None;
        for i in 0..MAX_RETRIES {
            let dst_update = self.build_update_client_on_dst(src_chain_height)?;
            info!(
                "[{}] sending updateClient to client hosted on dest. chain {} for height {} [try {}/{}]",
                self,
                self.dst_chain().id(),
                src_chain_height,
                i + 1, MAX_RETRIES,
            );

            let dst_tx_events = self.dst_chain().send_msgs(dst_update)?;
            info!("[{}] result {}\n", self, PrettyEvents(&dst_tx_events));

            dst_err_ev = dst_tx_events
                .into_iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));

            if dst_err_ev.is_none() {
                return Ok(());
            }
        }

        Err(LinkError::ClientError(ForeignClientError::ClientUpdate(
            format!(
                "Failed to update client on destination {} with err: {}",
                self.dst_chain().id(),
                dst_err_ev.unwrap()
            ),
        )))
    }

    /// Handles updating the client on the source chain
    fn update_client_src(&self, dst_chain_height: Height) -> Result<(), LinkError> {
        if self
            .src_chain()
            .proven_client_consensus(self.src_client_id(), dst_chain_height, Height::zero())
            .is_ok()
        {
            return Ok(());
        }

        let mut src_err_ev = None;
        for _ in 0..MAX_RETRIES {
            let src_update = self.build_update_client_on_src(dst_chain_height)?;
            info!(
                "[{}] sending updateClient to client hosted on src. chain {} for height {}",
                self,
                self.src_chain().id(),
                dst_chain_height,
            );

            let src_tx_events = self.src_chain().send_msgs(src_update)?;
            info!("[{}] result {}\n", self, PrettyEvents(&src_tx_events));

            src_err_ev = src_tx_events
                .into_iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));

            if src_err_ev.is_none() {
                return Ok(());
            }
        }

        Err(LinkError::ClientError(ForeignClientError::ClientUpdate(
            format!(
                "Failed to update client on source {} with err: {}",
                self.src_chain().id(),
                src_err_ev.unwrap()
            ),
        )))
    }

    /// Returns relevant packet events for building RecvPacket and timeout messages.
    /// Additionally returns the height (on source chain) corresponding to these events.
    fn target_height_and_send_packet_events(
        &self,
        opt_query_height: Option<Height>,
    ) -> Result<(Vec<IbcEvent>, Height), LinkError> {
        let mut events_result = vec![];

        let src_channel_id = self.src_channel_id()?;

        // Query packet commitments on source chain that have not been acknowledged
        let pc_request = QueryPacketCommitmentsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: src_channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };
        let (packet_commitments, src_response_height) =
            self.src_chain().query_packet_commitments(pc_request)?;

        let query_height = opt_query_height.unwrap_or(src_response_height);

        if packet_commitments.is_empty() {
            return Ok((events_result, query_height));
        }
        let commit_sequences: Vec<u64> = packet_commitments.iter().map(|p| p.sequence).collect();

        // Get the packets that have not been received on destination chain
        let request = QueryUnreceivedPacketsRequest {
            port_id: self.dst_port_id().to_string(),
            channel_id: self.dst_channel_id()?.to_string(),
            packet_commitment_sequences: commit_sequences.clone(),
        };

        let sequences: Vec<Sequence> = self
            .dst_chain()
            .query_unreceived_packets(request)?
            .into_iter()
            .map(From::from)
            .collect();

        if sequences.is_empty() {
            return Ok((events_result, query_height));
        }

        debug!(
            "[{}] packets that still have commitments on {}: {} (first 10 shown here; total={})",
            self,
            self.src_chain().id(),
            commit_sequences.iter().take(10).join(", "),
            commit_sequences.len()
        );

        debug!(
            "[{}] recv packets to send out to {} of the ones with commitments on source {}: {} (first 10 shown here; total={})",
            self,
            self.dst_chain().id(),
            self.src_chain().id(),
            sequences.iter().take(10).join(", "), sequences.len()
        );

        let query = QueryTxRequest::Packet(QueryPacketEventDataRequest {
            event_id: IbcEventType::SendPacket,
            source_port_id: self.src_port_id().clone(),
            source_channel_id: src_channel_id.clone(),
            destination_port_id: self.dst_port_id().clone(),
            destination_channel_id: self.dst_channel_id()?.clone(),
            sequences,
            height: query_height,
        });

        events_result = self.src_chain().query_txs(query)?;

        let mut packet_sequences = vec![];
        for event in events_result.iter() {
            let send_event = downcast!(event => IbcEvent::SendPacket)
                .ok_or_else(|| LinkError::Failed("unexpected query tx response".into()))?;
            packet_sequences.push(send_event.packet.sequence);
            if packet_sequences.len() > 10 {
                // Enough to print the first 10
                break;
            }
        }
        info!(
            "[{}] found unprocessed SendPacket events for {:?} (first 10 shown here; total={})",
            self,
            packet_sequences,
            events_result.len()
        );

        Ok((events_result, query_height))
    }

    /// Returns relevant packet events for building ack messages.
    /// Additionally returns the height (on source chain) corresponding to these events.
    fn target_height_and_write_ack_events(
        &self,
        opt_query_height: Option<Height>,
    ) -> Result<(Vec<IbcEvent>, Height), LinkError> {
        let mut events_result = vec![];

        let src_channel_id = self.src_channel_id()?;
        let dst_channel_id = self.dst_channel_id()?;

        // Get the sequences of packets that have been acknowledged on source
        let pc_request = QueryPacketAcknowledgementsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: src_channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };
        let (acks_on_source, src_response_height) = self
            .src_chain()
            .query_packet_acknowledgements(pc_request)
            .map_err(|e| LinkError::QueryError(self.src_chain().id(), e))?;

        let query_height = opt_query_height.unwrap_or(src_response_height);

        if acks_on_source.is_empty() {
            return Ok((events_result, query_height));
        }

        let mut acked_sequences: Vec<u64> = acks_on_source.iter().map(|p| p.sequence).collect();
        acked_sequences.sort_unstable();

        let request = QueryUnreceivedAcksRequest {
            port_id: self.dst_port_id().to_string(),
            channel_id: dst_channel_id.to_string(),
            packet_ack_sequences: acked_sequences.clone(),
        };

        let sequences: Vec<Sequence> = self
            .dst_chain()
            .query_unreceived_acknowledgement(request)
            .map_err(|e| LinkError::QueryError(self.dst_chain().id(), e))?
            .into_iter()
            .map(From::from)
            .collect();

        if sequences.is_empty() {
            return Ok((events_result, query_height));
        }

        debug!(
            "[{}] packets that have acknowledgments on {}: [{:?}..{:?}] (total={})",
            self,
            self.src_chain().id(),
            acked_sequences.first(),
            acked_sequences.last(),
            acked_sequences.len()
        );

        debug!(
            "[{}] ack packets to send out to {} of the ones with acknowledgments on {}: {} (first 10 shown here; total={})",
            self,
            self.dst_chain().id(),
            self.src_chain().id(),
            sequences.iter().take(10).join(", "), sequences.len()
        );

        events_result = self
            .src_chain()
            .query_txs(QueryTxRequest::Packet(QueryPacketEventDataRequest {
                event_id: IbcEventType::WriteAck,
                source_port_id: self.dst_port_id().clone(),
                source_channel_id: dst_channel_id.clone(),
                destination_port_id: self.src_port_id().clone(),
                destination_channel_id: src_channel_id.clone(),
                sequences,
                height: query_height,
            }))
            .map_err(|e| LinkError::QueryError(self.src_chain().id(), e))?;

        let mut packet_sequences = vec![];
        for event in events_result.iter() {
            let write_ack_event = downcast!(event => IbcEvent::WriteAcknowledgement)
                .ok_or_else(|| LinkError::Failed("unexpected query tx response".into()))?;
            packet_sequences.push(write_ack_event.packet.sequence);
            if packet_sequences.len() > 10 {
                // Enough to print the first 10
                break;
            }
        }
        info!("[{}] found unprocessed WriteAcknowledgement events for {:?} (first 10 shown here; total={})", self, packet_sequences, events_result.len());

        Ok((events_result, query_height))
    }

    /// Schedules the relaying of RecvPacket and Timeout messages.
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn build_recv_packet_and_timeout_msgs(
        &mut self,
        opt_query_height: Option<Height>,
    ) -> Result<(), LinkError> {
        // Get the events for the send packets on source chain that have not been received on
        // destination chain (i.e. ack was not seen on source chain).
        let (mut events, height) = self.target_height_and_send_packet_events(opt_query_height)?;

        // Skip: no relevant events found.
        if events.is_empty() {
            return Ok(());
        }

        for event in events.iter_mut() {
            event.set_height(height);
        }

        self.events_to_operational_data(events)?;

        Ok(())
    }

    /// Schedules the relaying of packet acknowledgment messages.
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn build_packet_ack_msgs(
        &mut self,
        opt_query_height: Option<Height>,
    ) -> Result<(), LinkError> {
        // Get the sequences of packets that have been acknowledged on destination chain but still
        // have commitments on source chain (i.e. ack was not seen on source chain)
        let (mut events, height) = self.target_height_and_write_ack_events(opt_query_height)?;

        // Skip: no relevant events found.
        if events.is_empty() {
            return Ok(());
        }

        for event in events.iter_mut() {
            event.set_height(height);
        }

        self.events_to_operational_data(events)?;
        Ok(())
    }

    fn build_recv_packet(&self, packet: &Packet, height: Height) -> Result<Option<Any>, LinkError> {
        let (_, proofs) = self
            .src_chain()
            .build_packet_proofs(
                PacketMsgType::Recv,
                &packet.source_port,
                &packet.source_channel,
                packet.sequence,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.src_chain().id(), e))?;

        let msg = MsgRecvPacket::new(packet.clone(), proofs.clone(), self.dst_signer()?);

        trace!(
            "[{}] built recv_packet msg {}, proofs at height {}",
            self,
            msg.packet,
            proofs.height()
        );

        Ok(Some(msg.to_any()))
    }

    fn build_ack_from_recv_event(
        &self,
        event: &WriteAcknowledgement,
    ) -> Result<Option<Any>, LinkError> {
        let packet = event.packet.clone();

        let (_, proofs) = self
            .src_chain()
            .build_packet_proofs(
                PacketMsgType::Ack,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                event.height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.src_chain().id(), e))?;

        let msg = MsgAcknowledgement::new(
            packet,
            event.ack.clone(),
            proofs.clone(),
            self.dst_signer()?,
        );

        trace!(
            "[{}] built acknowledgment msg {}, proofs at height {}",
            self,
            msg.packet,
            proofs.height()
        );

        Ok(Some(msg.to_any()))
    }

    fn build_timeout_packet(
        &self,
        packet: &Packet,
        height: Height,
    ) -> Result<Option<Any>, LinkError> {
        let dst_channel_id = self.dst_channel_id()?;

        let (packet_type, next_sequence_received) = if self.ordered_channel() {
            let next_seq = self
                .dst_chain()
                .query_next_sequence_receive(QueryNextSequenceReceiveRequest {
                    port_id: self.dst_port_id().to_string(),
                    channel_id: dst_channel_id.to_string(),
                })
                .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;
            (PacketMsgType::TimeoutOrdered, next_seq)
        } else {
            (PacketMsgType::TimeoutUnordered, packet.sequence)
        };

        let (_, proofs) = self
            .dst_chain()
            .build_packet_proofs(
                packet_type,
                &packet.destination_port,
                &packet.destination_channel,
                next_sequence_received,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.dst_chain().id(), e))?;

        let msg = MsgTimeout::new(
            packet.clone(),
            next_sequence_received,
            proofs.clone(),
            self.src_signer()?,
        );

        trace!(
            "[{}] built timeout msg {}, proofs at height {}",
            self,
            msg.packet,
            proofs.height()
        );

        Ok(Some(msg.to_any()))
    }

    fn build_timeout_on_close_packet(
        &self,
        packet: &Packet,
        height: Height,
    ) -> Result<Option<Any>, LinkError> {
        let (_, proofs) = self
            .dst_chain()
            .build_packet_proofs(
                PacketMsgType::TimeoutOnClose,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                height,
            )
            .map_err(|e| LinkError::PacketProofsConstructor(self.dst_chain().id(), e))?;

        let msg = MsgTimeoutOnClose::new(
            packet.clone(),
            packet.sequence,
            proofs.clone(),
            self.src_signer()?,
        );

        trace!(
            "[{}] built timeout on close msg {}, proofs at height {}",
            self,
            msg.packet,
            proofs.height()
        );

        Ok(Some(msg.to_any()))
    }

    fn build_timeout_from_send_packet_event(
        &self,
        event: &SendPacket,
        dst_chain_height: Height,
    ) -> Result<Option<Any>, LinkError> {
        let packet = event.packet.clone();
        if self
            .dst_channel(dst_chain_height)?
            .state_matches(&ChannelState::Closed)
        {
            Ok(self.build_timeout_on_close_packet(&event.packet, dst_chain_height)?)
        } else if packet.timed_out(dst_chain_height) {
            Ok(self.build_timeout_packet(&event.packet, dst_chain_height)?)
        } else {
            Ok(None)
        }
    }

    fn build_recv_or_timeout_from_send_packet_event(
        &self,
        event: &SendPacket,
        dst_chain_height: Height,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        let timeout = self.build_timeout_from_send_packet_event(event, dst_chain_height)?;
        if timeout.is_some() {
            Ok((None, timeout))
        } else {
            Ok((self.build_recv_packet(&event.packet, event.height)?, None))
        }
    }

    /// Checks if there are any operational data items ready, and if so performs the relaying
    /// of corresponding packets to the target chain.
    pub fn execute_schedule(&mut self) -> Result<RelaySummary, LinkError> {
        let (src_ods, dst_ods) = self.try_fetch_scheduled_operational_data();

        let mut summary = RelaySummary::empty();

        for od in dst_ods {
            summary.extend(self.relay_from_operational_data(od)?);
        }

        for od in src_ods {
            summary.extend(self.relay_from_operational_data(od)?);
        }

        Ok(summary)
    }

    /// Refreshes the scheduled batches.
    /// Verifies if any sendPacket messages timed-out. If so, moves them from destination op. data
    /// to source operational data, and adjusts the events and messages accordingly.
    pub fn refresh_schedule(&mut self) -> Result<(), LinkError> {
        let dst_current_height = self.dst_latest_height()?;

        // Intermediary data struct to help better manage the transfer from dst. operational data
        // to source operational data.
        let mut all_dst_odata = self.dst_operational_data.clone();

        let mut timed_out: HashMap<usize, Vec<TransitMessage>> = HashMap::default();

        // For each operational data targeting the destination chain...
        for (odata_pos, odata) in all_dst_odata.iter_mut().enumerate() {
            // ... check each `SendPacket` event, whether it should generate a timeout message
            let mut retain_batch = vec![];

            for gm in odata.batch.iter() {
                let TransitMessage { event, .. } = gm;

                match event {
                    IbcEvent::SendPacket(e) => {
                        // Catch any SendPacket event that timed-out
                        if self.send_packet_event_handled(e)? {
                            debug!(
                                "[{}] refreshing schedule: already handled send packet {}",
                                self, e
                            );
                        } else if let Some(new_msg) =
                            self.build_timeout_from_send_packet_event(e, dst_current_height)?
                        {
                            debug!(
                                "[{}] refreshing schedule: found a timed-out msg in the op data {}",
                                self, odata
                            );
                            timed_out.entry(odata_pos).or_insert_with(Vec::new).push(
                                TransitMessage {
                                    event: event.clone(),
                                    msg: new_msg,
                                },
                            );
                        } else {
                            // A SendPacket event, but did not time-out yet, retain
                            retain_batch.push(gm.clone());
                        }
                    }
                    IbcEvent::WriteAcknowledgement(e) => {
                        if self.write_ack_event_handled(e)? {
                            debug!(
                                "[{}] refreshing schedule: already handled {} write ack ",
                                self, e
                            );
                        } else {
                            retain_batch.push(gm.clone());
                        }
                    }
                    _ => retain_batch.push(gm.clone()),
                }
            }

            // Update the whole batch, keeping only the relevant ones
            odata.batch = retain_batch;
        }

        // Replace the original operational data with the updated one
        self.dst_operational_data = all_dst_odata;
        // Possibly some op. data became empty (if no events were kept).
        // Retain only the non-empty ones.
        self.dst_operational_data.retain(|o| !o.batch.is_empty());

        // Handle timed-out events
        if timed_out.is_empty() {
            // Nothing timed out in the meantime
            return Ok(());
        }

        // Schedule new operational data targeting the source chain
        for (_, batch) in timed_out.into_iter() {
            let mut new_od =
                OperationalData::new(dst_current_height, OperationalDataTarget::Source);

            new_od.batch = batch;

            info!(
                "[{}] refreshing schedule: re-scheduling from new timed-out batch of size {}",
                self,
                new_od.batch.len()
            );

            self.schedule_operational_data(new_od)?;
        }

        Ok(())
    }

    /// Adds a new operational data item for this relaying path to process later.
    /// If the relaying path has non-zero packet delays, this method also updates the client on the
    /// target chain with the appropriate headers.
    fn schedule_operational_data(&mut self, mut od: OperationalData) -> Result<(), LinkError> {
        if od.batch.is_empty() {
            info!(
                "[{}] ignoring operational data for {} because it has no messages",
                self, od.target
            );
            return Ok(());
        }

        info!(
            "[{}] scheduling op. data with {} msg(s) for {} (height {})",
            self,
            od.batch.len(),
            od.target,
            od.proofs_height.increment(), // increment for easier correlation with the client logs
        );

        // Update clients ahead of scheduling the operational data, if the delays are non-zero.
        if !self.zero_delay() {
            let target_height = od.proofs_height.increment();
            match od.target {
                OperationalDataTarget::Source => self.update_client_src(target_height)?,
                OperationalDataTarget::Destination => self.update_client_dst(target_height)?,
            };
        }

        od.scheduled_time = Instant::now();

        match od.target {
            OperationalDataTarget::Source => self.src_operational_data.push(od),
            OperationalDataTarget::Destination => self.dst_operational_data.push(od),
        };

        Ok(())
    }

    /// Pulls out the operational elements with elapsed delay period and that can
    /// now be processed. Does not block: if no OD fulfilled the delay period (or none is
    /// scheduled), returns immediately with `vec![]`.
    fn try_fetch_scheduled_operational_data(
        &mut self,
    ) -> (Vec<OperationalData>, Vec<OperationalData>) {
        // The first elements of the op. data vector contain the oldest entry.
        // Remove and return the elements with elapsed delay.

        let src_ods: Vec<OperationalData> = self
            .src_operational_data
            .iter()
            .filter(|op| op.scheduled_time.elapsed() > self.channel.connection_delay)
            .cloned()
            .collect();

        self.src_operational_data = self.src_operational_data[src_ods.len()..].to_owned();

        let dst_ods: Vec<OperationalData> = self
            .dst_operational_data
            .iter()
            .filter(|op| op.scheduled_time.elapsed() > self.channel.connection_delay)
            .cloned()
            .collect();

        self.dst_operational_data = self.dst_operational_data[dst_ods.len()..].to_owned();

        (src_ods, dst_ods)
    }

    /// Fetches an operational data that has fulfilled its predefined delay period. May _block_
    /// waiting for the delay period to pass.
    /// Returns `None` if there is no operational data scheduled.
    pub(crate) fn fetch_scheduled_operational_data(&mut self) -> Option<OperationalData> {
        let odata = self
            .src_operational_data
            .first()
            .or_else(|| self.dst_operational_data.first());

        if let Some(odata) = odata {
            // Check if the delay period did not completely elapse
            let delay_left = self
                .channel
                .connection_delay
                .checked_sub(odata.scheduled_time.elapsed());

            match delay_left {
                None => info!(
                    "[{}] ready to fetch a scheduled op. data with batch of size {} targeting {}",
                    self,
                    odata.batch.len(),
                    odata.target,
                ),
                Some(delay_left) => {
                    info!(
                        "[{}] waiting ({:?} left) for a scheduled op. data with batch of size {} targeting {}",
                        self,
                        delay_left,
                        odata.batch.len(),
                        odata.target,
                    );

                    // Wait until the delay period passes
                    thread::sleep(delay_left);
                }
            }

            let op = match odata.target {
                OperationalDataTarget::Source => self.src_operational_data.remove(0),
                OperationalDataTarget::Destination => self.dst_operational_data.remove(0),
            };

            Some(op)
        } else {
            None
        }
    }

    fn restore_src_client(&self) -> ForeignClient {
        ForeignClient::restore(
            self.src_client_id().clone(),
            self.src_chain().clone(),
            self.dst_chain().clone(),
        )
    }

    fn restore_dst_client(&self) -> ForeignClient {
        ForeignClient::restore(
            self.dst_client_id().clone(),
            self.dst_chain().clone(),
            self.src_chain().clone(),
        )
    }
}

impl fmt::Display for RelayPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let channel_id = self
            .src_channel_id()
            .map(ToString::to_string)
            .unwrap_or_else(|_| "None".to_string());

        write!(
            f,
            "{}:{}/{} -> {}",
            self.src_chain().id(),
            self.src_port_id(),
            channel_id,
            self.dst_chain().id()
        )
    }
}
