use std::collections::{HashMap, VecDeque};
use std::time::Instant;
use std::{fmt, thread};

use itertools::Itertools;
use prost_types::Any;
use tracing::{debug, error, info, trace};

use ibc::tagged::Tagged;
use ibc::{
    events::{IbcEvent, PrettyEvents},
    ics04_channel::{
        channel::{Order, QueryPacketEventDataRequest, State as ChannelState},
        events::{TaggedSendPacket, TaggedWriteAcknowledgement},
        msgs::{
            acknowledgement::MsgAcknowledgement, chan_close_confirm::MsgChannelCloseConfirm,
            recv_packet::MsgRecvPacket, timeout::MsgTimeout, timeout_on_close::MsgTimeoutOnClose,
        },
        packet::{PacketMsgType, Sequence, TaggedPacket},
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
    QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

use crate::chain::handle::ChainHandle;
use crate::channel::error::ChannelError;
use crate::channel::{Channel, ChannelEnd};
use crate::event::monitor::EventBatch;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::link::error::{self, LinkError};
use crate::link::operational_data::{
    DstOperationPayload, OperationalData, OperationalDataTarget, SrcOperationPayload,
};
use crate::link::relay_summary::RelaySummary;

const MAX_RETRIES: usize = 5;

pub struct RelayPath<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    channel: Channel<ChainA, ChainB>,
    // Marks whether this path has already cleared pending packets.
    // Packets should be cleared once (at startup), then this
    // flag turns to `false`.
    clear_packets: bool,
    // Operational data, targeting both the source and destination chain.
    // These vectors of operational data are ordered decreasingly by their age, with element at
    // position `0` being the oldest.
    // The operational data targeting the source chain comprises mostly timeout packet messages.
    src_operational_data: VecDeque<SrcOperationPayload<ChainA, ChainB>>,
    // The operational data targeting the destination chain comprises mostly RecvPacket and Ack msgs.
    dst_operational_data: VecDeque<DstOperationPayload<ChainA, ChainB>>,
}

impl<ChainA, ChainB> RelayPath<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    pub fn new(channel: Channel<ChainA, ChainB>) -> Self {
        Self {
            channel,
            clear_packets: true,
            src_operational_data: VecDeque::new(),
            dst_operational_data: VecDeque::new(),
        }
    }

    pub fn src_chain(&self) -> &ChainA {
        self.channel.src_chain()
    }

    pub fn dst_chain(&self) -> &ChainB {
        self.channel.dst_chain()
    }

    pub fn src_client_id(&self) -> Tagged<ChainA, ClientId> {
        self.channel.src_client_id()
    }

    pub fn dst_client_id(&self) -> Tagged<ChainB, ClientId> {
        self.channel.dst_client_id()
    }

    pub fn src_connection_id(&self) -> Tagged<ChainA, ConnectionId> {
        self.channel.src_connection_id()
    }

    pub fn dst_connection_id(&self) -> Tagged<ChainB, ConnectionId> {
        self.channel.dst_connection_id()
    }

    pub fn src_port_id(&self) -> Tagged<ChainA, PortId> {
        self.channel.src_port_id()
    }

    pub fn dst_port_id(&self) -> Tagged<ChainB, PortId> {
        self.channel.dst_port_id()
    }

    pub fn src_channel_id(&self) -> Result<Tagged<ChainA, ChannelId>, LinkError> {
        self.channel
            .src_channel_id()
            .ok_or_else(|| LinkError::missing_channel_id(self.src_chain().id().untag()))
    }

    pub fn dst_channel_id(&self) -> Result<Tagged<ChainB, ChannelId>, LinkError> {
        self.channel
            .dst_channel_id()
            .ok_or_else(|| LinkError::missing_channel_id(self.dst_chain().id().untag()))
    }

    pub fn channel(&self) -> &Channel<ChainA, ChainB> {
        &self.channel
    }

    fn src_channel(
        &self,
        height: Tagged<ChainA, Height>,
    ) -> Result<ChannelEnd<ChainA, ChainB>, LinkError> {
        self.src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id()?, height)
            .map_err(|e| LinkError::channel(ChannelError::query(self.src_chain().id().untag(), e)))
    }

    fn dst_channel(
        &self,
        height: Tagged<ChainB, Height>,
    ) -> Result<ChannelEnd<ChainB, ChainA>, LinkError> {
        self.dst_chain()
            .query_channel(self.dst_port_id(), self.dst_channel_id()?, height)
            .map_err(|e| LinkError::channel(ChannelError::query(self.src_chain().id().untag(), e)))
    }

    fn src_signer(&self) -> Result<Tagged<ChainA, Signer>, LinkError> {
        self.src_chain()
            .get_signer()
            .map_err(|e| LinkError::signer(self.src_chain().id().untag(), e))
    }

    fn dst_signer(&self) -> Result<Tagged<ChainB, Signer>, LinkError> {
        self.dst_chain()
            .get_signer()
            .map_err(|e| LinkError::signer(self.dst_chain().id().untag(), e))
    }

    pub fn dst_latest_height(&self) -> Result<Tagged<ChainB, Height>, LinkError> {
        self.dst_chain()
            .query_latest_height()
            .map_err(|e| LinkError::query(self.dst_chain().id().untag(), e))
    }

    fn unordered_channel(&self) -> bool {
        self.channel.ordering == Order::Unordered
    }

    fn ordered_channel(&self) -> bool {
        self.channel.ordering == Order::Ordered
    }

    pub fn build_update_client_on_dst(
        &self,
        height: Tagged<ChainA, Height>,
    ) -> Result<Vec<Tagged<ChainB, Any>>, LinkError> {
        let client = self.restore_dst_client();
        client
            .build_update_client(height)
            .map_err(LinkError::client)
    }

    pub fn build_update_client_on_src(
        &self,
        height: Tagged<ChainB, Height>,
    ) -> Result<Vec<Tagged<ChainA, Any>>, LinkError> {
        let client = self.restore_src_client();
        client
            .build_update_client(height)
            .map_err(LinkError::client)
    }

    fn build_chan_close_confirm_from_event(
        &self,
        event: Tagged<ChainA, IbcEvent>,
    ) -> Result<Tagged<ChainB, Any>, LinkError> {
        let src_channel_id = self.src_channel_id()?;
        let event_height = event.map(|e| e.height());

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, event_height)
            .map_err(|e| LinkError::channel(ChannelError::channel_proof(e)))?;

        // Build the domain type message
        let new_msg = MsgChannelCloseConfirm::tagged_new(
            self.dst_port_id(),
            self.dst_channel_id()?,
            proofs,
            self.dst_signer()?,
        );

        Ok(new_msg.map_into(Msg::to_any))
    }

    // Determines if the events received are relevant and should be processed.
    // Only events for a port/channel matching one of the channel ends should be processed.
    fn filter_events(
        &self,
        events: Vec<Tagged<ChainA, IbcEvent>>,
    ) -> Vec<Tagged<ChainA, IbcEvent>> {
        let mut result = vec![];

        let src_channel_id = if let Ok(some_id) = self.src_channel_id() {
            some_id
        } else {
            return vec![];
        };

        for event in events.iter() {
            // FIXME: Match the events with tagged identifiers instead of over raw values
            match event.value() {
                IbcEvent::SendPacket(send_packet_ev) => {
                    if src_channel_id.value() == send_packet_ev.src_channel_id()
                        && self.src_port_id().value() == send_packet_ev.src_port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                    if src_channel_id.value() == write_ack_ev.dst_channel_id()
                        && self.src_port_id().value() == write_ack_ev.dst_port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::CloseInitChannel(chan_close_ev) => {
                    if src_channel_id.value() == chan_close_ev.channel_id()
                        && self.src_port_id().value() == chan_close_ev.port_id()
                    {
                        result.push(event.clone());
                    }
                }
                IbcEvent::TimeoutPacket(timeout_ev) => {
                    if src_channel_id.value() == timeout_ev.src_channel_id()
                        && self.channel.src_port_id().value() == timeout_ev.src_port_id()
                    {
                        result.push(event.clone());
                    }
                }
                _ => {}
            }
        }
        result
    }

    fn relay_pending_packets(
        &mut self,
        height: Option<Tagged<ChainA, Height>>,
    ) -> Result<(), LinkError> {
        for _ in 0..MAX_RETRIES {
            let cleared = self
                .build_recv_packet_and_timeout_msgs(height)
                .and_then(|()| self.build_packet_ack_msgs(height))
                .is_ok();

            if cleared {
                return Ok(());
            }
        }
        Err(LinkError::old_packet_clearing_failed())
    }

    /// Clears any packets that were sent before `height`, either if the `clear_packets` flag
    /// is set or if clearing is forced by the caller.
    pub fn schedule_packet_clearing(
        &mut self,
        height: Option<Tagged<ChainA, Height>>,
        force: bool,
    ) -> Result<(), LinkError> {
        if self.clear_packets || force {
            // Disable further clearing of old packets by default.
            // Clearing may still happen: upon new blocks, when `force = true`.
            self.clear_packets = false;

            let clear_height = height
                .map(|h| {
                    h.map(|h| h.decrement())
                        .transpose()
                        .map_err(|e| LinkError::decrement_height(h.value().clone(), e))
                })
                .transpose()?;

            info!(height = ?clear_height, "[{}] clearing pending packets", self);

            self.relay_pending_packets(clear_height)?;

            info!(height = ?clear_height, "[{}] finished scheduling pending packets clearing", self);
        }

        Ok(())
    }

    /// Generate & schedule operational data from the input `batch` of IBC events.
    pub fn update_schedule(&mut self, batch: Tagged<ChainA, EventBatch>) -> Result<(), LinkError> {
        // Collect relevant events from the incoming batch & adjust their height.
        let events = self.filter_events(batch.map_into(|b| b.events).transpose());

        // Transform the events into operational data items
        self.events_to_operational_data(events)
    }

    /// Produces and schedules operational data for this relaying path based on the input events.
    fn events_to_operational_data(
        &mut self,
        events: Vec<Tagged<ChainA, IbcEvent>>,
    ) -> Result<(), LinkError> {
        // Obtain the operational data for the source chain (mostly timeout packets) and for the
        // destination chain (e.g., receive packet messages).
        let (src_opt, dst_opt) = self.generate_operational_data(events)?;

        if let Some(src_od) = src_opt {
            self.schedule_operational_data(OperationalData::Src(src_od))?;
        }
        if let Some(dst_od) = dst_opt {
            self.schedule_operational_data(OperationalData::Dst(dst_od))?;
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
        input: Vec<Tagged<ChainA, IbcEvent>>,
    ) -> Result<
        (
            Option<SrcOperationPayload<ChainA, ChainB>>,
            Option<DstOperationPayload<ChainA, ChainB>>,
        ),
        LinkError,
    > {
        if !input.is_empty() {
            info!(
                "[{}] generate messages from batch with {} events",
                self,
                input.len()
            );
        }
        let src_height = match input.get(0) {
            None => return Ok((None, None)),
            Some(ev) => ev.map(|e| e.height()),
        };

        let dst_height = self.dst_latest_height()?;
        // Operational data targeting the source chain (e.g., Timeout packets)
        let mut src_od = SrcOperationPayload::new(dst_height);
        // Operational data targeting the destination chain (e.g., SendPacket messages)
        let mut dst_od = DstOperationPayload::new(src_height);

        for event in input {
            debug!("[{}] {} => {}", self, self.src_chain().id(), event);
            let (dst_msg, src_msg): (Option<Tagged<ChainB, Any>>, Option<Tagged<ChainA, Any>>) =
                match event.value() {
                    IbcEvent::CloseInitChannel(_) => {
                        (Some(self.build_chan_close_confirm_from_event(event)?), None)
                    }
                    IbcEvent::TimeoutPacket(timeout_ev) => {
                        let timeout_height = event.tag(timeout_ev.height);

                        // When a timeout packet for an ordered channel is processed on-chain (src here)
                        // the chain closes the channel but no close init event is emitted, instead
                        // we get a timeout packet event (this happens for both unordered and ordered channels)
                        // Here we check that the channel is closed on src and send a channel close confirm
                        // to the counterparty.
                        if self.ordered_channel()
                            && self
                                .src_channel(timeout_height)?
                                .value()
                                .state_matches(&ChannelState::Closed)
                        {
                            (Some(self.build_chan_close_confirm_from_event(event)?), None)
                        } else {
                            (None, None)
                        }
                    }
                    IbcEvent::SendPacket(send_packet_ev) => {
                        if self.send_packet_event_handled(TaggedSendPacket::from_tagged(
                            event.tag(send_packet_ev.clone()),
                        ))? {
                            debug!("[{}] {} already handled", self, send_packet_ev);
                            (None, None)
                        } else {
                            self.build_recv_or_timeout_from_send_packet_event(
                                TaggedSendPacket::from_tagged(event.tag(send_packet_ev.clone())),
                                dst_height,
                            )?
                        }
                    }
                    IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                        if self
                            .dst_channel(Height::tagged_zero())?
                            .value()
                            .state_matches(&ChannelState::Closed)
                        {
                            (None, None)
                        } else if self.write_ack_event_handled(
                            TaggedWriteAcknowledgement::from_tagged(
                                event.tag(write_ack_ev.clone()),
                            ),
                        )? {
                            debug!("[{}] {} already handled", self, write_ack_ev);
                            (None, None)
                        } else {
                            (
                                self.build_ack_from_recv_event(
                                    TaggedWriteAcknowledgement::from_tagged(
                                        event.tag(write_ack_ev.clone()),
                                    ),
                                )?,
                                None,
                            )
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
                    msg.value().type_url,
                    event
                );

                dst_od.batch.push((event, msg));
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
                        msg.value().type_url,
                        event
                    );
                    src_od.batch.push((event, msg));
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
        initial_od: OperationalData<ChainA, ChainB>,
    ) -> Result<RelaySummary, LinkError> {
        // We will operate on potentially different operational data if the initial one fails.
        let mut odata = initial_od;

        for i in 0..MAX_RETRIES {
            info!(
                "[{}] relay op. data of {} msgs(s) to {} (height {}), delayed by: {:?} [try {}/{}]",
                self,
                odata.batch_len(),
                odata.target(),
                odata.untagged_height().increment(),
                odata.scheduled_time().elapsed(),
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
                Err(LinkError(error::LinkErrorDetail::Send(e), _)) => {
                    // This error means we could retry
                    error!("[{}] error {}", self, e.event);
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
        initial_odata: OperationalData<ChainA, ChainB>,
    ) -> Option<OperationalData<ChainA, ChainB>> {
        info!(
            "[{}] failed. Regenerate operational data from {} events",
            self,
            initial_odata.batch_len()
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
            match initial_odata {
                OperationalData::Src(_) => {
                    // Our target is the _source_ chain, retry these messages
                    info!("[{}] will retry with op data {}", self, src_od);
                    return Some(OperationalData::Src(src_od));
                }
                OperationalData::Dst(_) => {
                    // Our target is the _destination_ chain, the data in `src_od` contains
                    // potentially new timeout messages that have to be handled separately.
                    if let Err(e) = self.schedule_operational_data(OperationalData::Src(src_od)) {
                        error!(
                            "[{}] failed to schedule newly-generated operational data from \
                        initial data: {} with error {}, discarding this op. data",
                            self, initial_odata, e
                        );
                        return None;
                    }
                }
            }
        }

        if let Some(dst_od) = dst_opt {
            match initial_odata {
                OperationalData::Src(_) => {
                    // Our target is the _source_ chain, but `dst_od` has new messages
                    // intended for the destination chain, this should never be the case
                    error!(
                        "[{}] generated new messages for destination chain while handling \
                        failed events targeting the source chain!",
                        self
                    );
                }
                OperationalData::Dst(_) => {
                    // Our target is the _destination_ chain, retry these messages
                    info!("[{}] will retry with op data {}", self, dst_od);
                    return Some(OperationalData::Dst(dst_od));
                }
            }
        } else {
            // There is no message intended for the destination chain
            if initial_odata.target() == OperationalDataTarget::Destination {
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
        odata: OperationalData<ChainA, ChainB>,
    ) -> Result<RelaySummary, LinkError> {
        if odata.is_empty_batch() {
            error!("[{}] ignoring empty operational data!", self);
            return Ok(RelaySummary::empty());
        }

        // let msgs = odata.assemble_msgs(self)?;

        let tx_events = match odata {
            OperationalData::Src(data) => {
                let messages = data.assemble_msgs(self)?;
                let events = self
                    .src_chain()
                    .send_msgs(messages)
                    .map_err(LinkError::relayer)?;
                events.untag()
            }
            OperationalData::Dst(data) => {
                let messages = data.assemble_msgs(self)?;
                let events = self
                    .dst_chain()
                    .send_msgs(messages)
                    .map_err(LinkError::relayer)?;
                events.untag()
            }
        };

        info!("[{}] result {}\n", self, PrettyEvents(&tx_events));

        let ev = tx_events
            .clone()
            .into_iter()
            .find(|event| matches!(event, IbcEvent::ChainError(_)));

        match ev {
            Some(ev) => Err(LinkError::send(ev)),
            None => Ok(RelaySummary::from_events(tx_events)),
        }
    }

    /// Checks if a sent packet has been received on destination.
    fn send_packet_received_on_dst(
        &self,
        packet: TaggedPacket<ChainB, ChainA>,
    ) -> Result<bool, LinkError> {
        let unreceived_packet = self
            .dst_chain()
            .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                port_id: self.dst_port_id().to_string(),
                channel_id: self.dst_channel_id()?.to_string(),
                packet_commitment_sequences: vec![packet.untag().sequence.into()],
            })
            .map_err(LinkError::relayer)?;

        Ok(unreceived_packet.value().is_empty())
    }

    /// Checks if a packet commitment has been cleared on source.
    /// The packet commitment is cleared when either an acknowledgment or a timeout is received on source.
    fn send_packet_commitment_cleared_on_src(
        &self,
        packet: TaggedPacket<ChainB, ChainA>,
    ) -> Result<bool, LinkError> {
        let (bytes, _) = self
            .src_chain()
            .build_incoming_packet_proofs(
                PacketMsgType::Recv,
                self.src_port_id(),
                self.src_channel_id()?,
                packet.sequence(),
                Height::tagged_zero(),
            )
            .map_err(LinkError::relayer)?;

        Ok(bytes.value().is_empty())
    }

    /// Checks if a send packet event has already been handled (e.g. by another relayer).
    fn send_packet_event_handled(
        &self,
        sp: TaggedSendPacket<ChainB, ChainA>,
    ) -> Result<bool, LinkError> {
        let packet = sp.packet();
        let is_received_on_dst = self.send_packet_received_on_dst(packet)?;
        let is_commitment_cleared_on_src = self.send_packet_commitment_cleared_on_src(packet)?;

        Ok(is_received_on_dst || is_commitment_cleared_on_src)
    }

    /// Checks if an acknowledgement for the given packet has been received on
    /// source chain of the packet, ie. the destination chain of the relay path
    /// that sends the acknowledgment.
    fn recv_packet_acknowledged_on_src(
        &self,
        packet: TaggedPacket<ChainA, ChainB>,
    ) -> Result<bool, LinkError> {
        let sequences = packet.sequence().map_into(|s| vec![s.to_u64()]);

        let unreceived_ack = self
            .dst_chain()
            .query_unreceived_acknowledgement(self.dst_port_id(), self.dst_channel_id()?, sequences)
            .map_err(LinkError::relayer)?;

        Ok(unreceived_ack.value().is_empty())
    }

    /// Checks if a receive packet event has already been handled (e.g. by another relayer).
    fn write_ack_event_handled(
        &self,
        rp: TaggedWriteAcknowledgement<ChainA, ChainB>,
    ) -> Result<bool, LinkError> {
        self.recv_packet_acknowledged_on_src(rp.packet())
    }

    /// Returns `true` if the delay for this relaying path is zero.
    /// Conversely, returns `false` if the delay is non-zero.
    pub fn zero_delay(&self) -> bool {
        self.channel.connection_delay == ZERO_DURATION
    }

    /// Handles updating the client on the destination chain
    fn update_client_dst(&self, src_chain_height: Tagged<ChainA, Height>) -> Result<(), LinkError> {
        // Handle the update on the destination chain
        // Check if a consensus state at update_height exists on destination chain already
        if self
            .dst_chain()
            .proven_client_consensus(
                self.dst_client_id(),
                src_chain_height,
                Height::tagged_zero(),
            )
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

            let dst_tx_events = self
                .dst_chain()
                .send_msgs(dst_update)
                .map_err(LinkError::relayer)?;

            info!(
                "[{}] result {}\n",
                self,
                PrettyEvents(dst_tx_events.value())
            );

            dst_err_ev = dst_tx_events
                .into_iter()
                .find(|event| matches!(event.value(), IbcEvent::ChainError(_)));

            if dst_err_ev.is_none() {
                return Ok(());
            }
        }

        Err(LinkError::client(ForeignClientError::chain_error_event(
            self.dst_chain().id().untag(),
            dst_err_ev.unwrap().untag(),
        )))
    }

    /// Handles updating the client on the source chain
    fn update_client_src(&self, dst_chain_height: Tagged<ChainB, Height>) -> Result<(), LinkError> {
        if self
            .src_chain()
            .proven_client_consensus(
                self.src_client_id(),
                dst_chain_height,
                Height::tagged_zero(),
            )
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

            let src_tx_events = self
                .src_chain()
                .send_msgs(src_update)
                .map_err(LinkError::relayer)?;
            info!(
                "[{}] result {}\n",
                self,
                PrettyEvents(src_tx_events.value())
            );

            src_err_ev = src_tx_events
                .into_iter()
                .find(|event| matches!(event.value(), IbcEvent::ChainError(_)));

            if src_err_ev.is_none() {
                return Ok(());
            }
        }

        Err(LinkError::client(ForeignClientError::chain_error_event(
            self.src_chain().id().untag(),
            src_err_ev.unwrap().untag(),
        )))
    }

    /// Returns relevant packet events for building RecvPacket and timeout messages.
    /// Additionally returns the height (on source chain) corresponding to these events.
    fn target_height_and_send_packet_events(
        &self,
        opt_query_height: Option<Tagged<ChainA, Height>>,
    ) -> Result<(Tagged<ChainA, Vec<IbcEvent>>, Tagged<ChainA, Height>), LinkError> {
        let mut events_result = Tagged::new(vec![]);

        let src_channel_id = self.src_channel_id()?;

        // Query packet commitments on source chain that have not been acknowledged
        let pc_request = QueryPacketCommitmentsRequest {
            port_id: self.src_port_id().to_string(),
            channel_id: src_channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };
        let (packet_commitments, src_response_height) = self
            .src_chain()
            .query_packet_commitments(pc_request)
            .map_err(LinkError::relayer)?;

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

        let sequences: Tagged<ChainB, Vec<Sequence>> = self
            .dst_chain()
            .query_unreceived_packets(request)
            .map_err(LinkError::relayer)?
            .map_into(|sequences| sequences.into_iter().map(Sequence::new).collect());

        if sequences.value().is_empty() {
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
            sequences.value().iter().take(10).join(", "), sequences.value().len()
        );

        let request = QueryPacketEventDataRequest::new_send_packet(
            src_channel_id,
            self.src_port_id(),
            self.dst_channel_id()?,
            self.dst_port_id(),
            sequences,
            query_height,
        );

        let query = request.map_into(QueryTxRequest::Packet);

        events_result = self
            .src_chain()
            .query_txs(query)
            .map_err(LinkError::relayer)?;

        let mut packet_sequences = vec![];
        for event in events_result.value().iter() {
            match event {
                IbcEvent::SendPacket(send_event) => {
                    packet_sequences.push(send_event.packet.sequence);
                    if packet_sequences.len() > 10 {
                        // Enough to print the first 10
                        break;
                    }
                }
                _ => return Err(LinkError::unexpected_event(event.clone())),
            }
        }
        info!(
            "[{}] found unprocessed SendPacket events for {:?} (first 10 shown here; total={})",
            self,
            packet_sequences,
            events_result.value().len()
        );

        Ok((events_result, query_height))
    }

    /// Returns relevant packet events for building ack messages.
    /// Additionally returns the height (on source chain) corresponding to these events.
    fn target_height_and_write_ack_events(
        &self,
        opt_query_height: Option<Tagged<ChainA, Height>>,
    ) -> Result<(Tagged<ChainA, Vec<IbcEvent>>, Tagged<ChainA, Height>), LinkError> {
        let mut events_result = Tagged::new(vec![]);

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
            .map_err(|e| LinkError::query(self.src_chain().id().untag(), e))?;

        let query_height = opt_query_height.unwrap_or(src_response_height);

        if acks_on_source.value().is_empty() {
            return Ok((events_result, query_height));
        }

        let acked_sequences = acks_on_source.map_into(|packets| {
            let mut sequences: Vec<u64> = packets.into_iter().map(|p| p.sequence).collect();
            sequences.sort_unstable();
            sequences
        });

        let sequences = self
            .dst_chain()
            .query_unreceived_acknowledgement(self.dst_port_id(), dst_channel_id, acked_sequences)
            .map_err(|e| LinkError::query(self.dst_chain().id().untag(), e))?;

        if sequences.value().is_empty() {
            return Ok((events_result, query_height));
        }

        debug!(
            "[{}] packets that have acknowledgments on {}: [{:?}..{:?}] (total={})",
            self,
            self.src_chain().id(),
            acked_sequences.value().first(),
            acked_sequences.value().last(),
            acked_sequences.value().len()
        );

        debug!(
            "[{}] ack packets to send out to {} of the ones with acknowledgments on {}: {} (first 10 shown here; total={})",
            self,
            self.dst_chain().id(),
            self.src_chain().id(),
            sequences.value().iter().take(10).join(", "), sequences.value().len()
        );

        let request = QueryPacketEventDataRequest::new_write_ack(
            dst_channel_id,
            self.dst_port_id(),
            src_channel_id,
            self.src_port_id(),
            sequences,
            query_height,
        );

        let query = request.map_into(QueryTxRequest::Packet);

        events_result = self
            .src_chain()
            .query_txs(query)
            .map_err(|e| LinkError::query(self.src_chain().id().untag(), e))?;

        let mut packet_sequences = vec![];
        for event in events_result.value().iter() {
            match event {
                IbcEvent::WriteAcknowledgement(write_ack_event) => {
                    packet_sequences.push(write_ack_event.packet.sequence);
                    if packet_sequences.len() > 10 {
                        // Enough to print the first 10
                        break;
                    }
                }
                _ => {
                    return Err(LinkError::unexpected_event(event.clone()));
                }
            }
        }
        info!("[{}] found unprocessed WriteAcknowledgement events for {:?} (first 10 shown here; total={})",
            self, packet_sequences, events_result.value().len());

        Ok((events_result, query_height))
    }

    /// Schedules the relaying of RecvPacket and Timeout messages.
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn build_recv_packet_and_timeout_msgs(
        &mut self,
        opt_query_height: Option<Tagged<ChainA, Height>>,
    ) -> Result<(), LinkError> {
        // Get the events for the send packets on source chain that have not been received on
        // destination chain (i.e. ack was not seen on source chain).
        let (events, height) = self.target_height_and_send_packet_events(opt_query_height)?;

        let events = events
            .map_into(|events| {
                events
                    .into_iter()
                    .map(|mut e| {
                        e.set_height(height.value().clone());
                        e
                    })
                    .collect::<Vec<_>>()
            })
            .transpose();

        if !events.is_empty() {
            self.events_to_operational_data(events)?;
        }

        Ok(())
    }

    /// Schedules the relaying of packet acknowledgment messages.
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn build_packet_ack_msgs(
        &mut self,
        opt_query_height: Option<Tagged<ChainA, Height>>,
    ) -> Result<(), LinkError> {
        // Get the sequences of packets that have been acknowledged on destination chain but still
        // have commitments on source chain (i.e. ack was not seen on source chain)
        let (events, height) = self.target_height_and_write_ack_events(opt_query_height)?;

        let events = events
            .map_into(|events| {
                events
                    .into_iter()
                    .map(|mut e| {
                        e.set_height(height.value().clone());
                        e
                    })
                    .collect::<Vec<_>>()
            })
            .transpose();

        if !events.is_empty() {
            self.events_to_operational_data(events)?;
        }

        Ok(())
    }

    fn build_recv_packet(
        &self,
        packet: TaggedPacket<ChainB, ChainA>,
        height: Tagged<ChainB, Height>,
    ) -> Result<Option<Tagged<ChainB, Any>>, LinkError> {
        let (_, proofs) = self
            .src_chain()
            .build_incoming_packet_proofs(
                PacketMsgType::Recv,
                packet.source_port(),
                packet.source_channel(),
                packet.sequence(),
                height,
            )
            .map_err(|e| LinkError::packet_proofs_constructor(self.src_chain().id().untag(), e))?;

        let msg = MsgRecvPacket::tagged_new(packet, proofs, self.dst_signer()?);

        trace!(
            "[{}] built recv_packet msg {}, proofs at height {}",
            self,
            msg.value().packet,
            proofs.value().height()
        );

        Ok(Some(msg.map_into(Msg::to_any)))
    }

    fn build_ack_from_recv_event(
        &self,
        event: TaggedWriteAcknowledgement<ChainA, ChainB>,
    ) -> Result<Option<Tagged<ChainB, Any>>, LinkError> {
        let packet = event.packet();

        let (_, proofs) = self
            .src_chain()
            .build_packet_proofs(
                PacketMsgType::Ack,
                packet.destination_port(),
                packet.destination_channel(),
                packet.sequence(),
                event.height(),
            )
            .map_err(|e| LinkError::packet_proofs_constructor(self.src_chain().id().untag(), e))?;

        let msg =
            MsgAcknowledgement::tagged_new(packet, event.ack(), proofs.clone(), self.dst_signer()?);

        trace!(
            "[{}] built acknowledgment msg {}, proofs at height {}",
            self,
            msg.value().packet,
            msg.value().proofs.height()
        );

        Ok(Some(msg.map_into(Msg::to_any)))
    }

    fn build_timeout_packet(
        &self,
        packet: TaggedPacket<ChainB, ChainA>,
        height: Tagged<ChainB, Height>,
    ) -> Result<Option<Tagged<ChainA, Any>>, LinkError> {
        let dst_channel_id = self.dst_channel_id()?;

        let (packet_type, next_sequence_received) = if self.ordered_channel() {
            let next_seq = self
                .dst_chain()
                .query_next_sequence_receive(QueryNextSequenceReceiveRequest {
                    port_id: self.dst_port_id().to_string(),
                    channel_id: dst_channel_id.to_string(),
                })
                .map_err(|e| LinkError::query(self.dst_chain().id().untag(), e))?;
            (PacketMsgType::TimeoutOrdered, next_seq)
        } else {
            (PacketMsgType::TimeoutUnordered, packet.sequence())
        };

        let (_, proofs) = self
            .dst_chain()
            .build_packet_proofs(
                packet_type,
                packet.destination_port(),
                packet.destination_channel(),
                next_sequence_received,
                height,
            )
            .map_err(|e| LinkError::packet_proofs_constructor(self.dst_chain().id().untag(), e))?;

        let msg =
            MsgTimeout::tagged_new(packet, next_sequence_received, proofs, self.src_signer()?);

        trace!(
            "[{}] built timeout msg {}, proofs at height {}",
            self,
            msg.value().packet,
            msg.value().proofs.height()
        );

        Ok(Some(msg.map_into(Msg::to_any)))
    }

    fn build_timeout_on_close_packet(
        &self,
        packet: TaggedPacket<ChainB, ChainA>,
        height: Tagged<ChainB, Height>,
    ) -> Result<Option<Tagged<ChainA, Any>>, LinkError> {
        let (_, proofs) = self
            .dst_chain()
            .build_packet_proofs(
                PacketMsgType::TimeoutOnClose,
                packet.destination_port(),
                packet.destination_channel(),
                packet.sequence(),
                height,
            )
            .map_err(|e| LinkError::packet_proofs_constructor(self.dst_chain().id().untag(), e))?;

        let next_sequence_recv = packet.sequence();

        let msg =
            MsgTimeoutOnClose::tagged_new(packet, next_sequence_recv, proofs, self.src_signer()?);

        trace!(
            "[{}] built timeout on close msg {}, proofs at height {}",
            self,
            msg.value().packet,
            msg.value().proofs.height()
        );

        Ok(Some(msg.map_into(Msg::to_any)))
    }

    fn build_timeout_from_send_packet_event(
        &self,
        event: TaggedSendPacket<ChainB, ChainA>,
        dst_chain_height: Tagged<ChainB, Height>,
    ) -> Result<Option<Tagged<ChainA, Any>>, LinkError> {
        let packet = event.packet();
        if self
            .dst_channel(dst_chain_height)?
            .value()
            .state_matches(&ChannelState::Closed)
        {
            Ok(self.build_timeout_on_close_packet(packet, dst_chain_height)?)
        } else if packet.timed_out(dst_chain_height) {
            Ok(self.build_timeout_packet(packet, dst_chain_height)?)
        } else {
            Ok(None)
        }
    }

    fn build_recv_or_timeout_from_send_packet_event(
        &self,
        event: TaggedSendPacket<ChainB, ChainA>,
        dst_chain_height: Tagged<ChainB, Height>,
    ) -> Result<(Option<Tagged<ChainB, Any>>, Option<Tagged<ChainA, Any>>), LinkError> {
        let timeout = self.build_timeout_from_send_packet_event(event, dst_chain_height)?;
        if timeout.is_some() {
            Ok((None, timeout))
        } else {
            Ok((
                self.build_recv_packet(event.packet(), event.height())?,
                None,
            ))
        }
    }

    /// Checks if there are any operational data items ready, and if so performs the relaying
    /// of corresponding packets to the target chain.
    pub fn execute_schedule(&mut self) -> Result<RelaySummary, LinkError> {
        let (src_ods, dst_ods) = self.try_fetch_scheduled_operational_data();

        let mut summary = RelaySummary::empty();

        for od in dst_ods {
            summary.extend(self.relay_from_operational_data(OperationalData::Dst(od))?);
        }

        for od in src_ods {
            summary.extend(self.relay_from_operational_data(OperationalData::Src(od))?);
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

        let mut timed_out: HashMap<usize, Vec<(Tagged<ChainA, IbcEvent>, Tagged<ChainA, Any>)>> =
            HashMap::default();

        // For each operational data targeting the destination chain...
        for (odata_pos, odata) in all_dst_odata.iter_mut().enumerate() {
            // ... check each `SendPacket` event, whether it should generate a timeout message
            let mut retain_batch = vec![];

            for gm in odata.batch.iter() {
                let (event, _) = gm;
                match event.value() {
                    IbcEvent::SendPacket(e) => {
                        let send_packet = TaggedSendPacket::from_tagged(event.tag(e.clone()));

                        // Catch any SendPacket event that timed-out
                        if self.send_packet_event_handled(send_packet)? {
                            debug!(
                                "[{}] refreshing schedule: already handled send packet {}",
                                self, e
                            );
                        } else if let Some(new_msg) = self
                            .build_timeout_from_send_packet_event(send_packet, dst_current_height)?
                        {
                            debug!(
                                "[{}] refreshing schedule: found a timed-out msg in the op data {}",
                                self, odata
                            );
                            timed_out
                                .entry(odata_pos)
                                .or_insert_with(Vec::new)
                                .push((event.clone(), new_msg));
                        } else {
                            // A SendPacket event, but did not time-out yet, retain
                            retain_batch.push(gm.clone());
                        }
                    }
                    IbcEvent::WriteAcknowledgement(e) => {
                        let event = TaggedWriteAcknowledgement::from_tagged(event.tag(e.clone()));

                        if self.write_ack_event_handled(event)? {
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
            let mut new_od: SrcOperationPayload<ChainA, ChainB> =
                SrcOperationPayload::new(dst_current_height);

            new_od.batch = batch;

            info!(
                "[{}] refreshing schedule: re-scheduling from new timed-out batch of size {}",
                self,
                new_od.batch.len()
            );

            self.schedule_operational_data(OperationalData::Src(new_od))?;
        }

        Ok(())
    }

    /// Adds a new operational data item for this relaying path to process later.
    /// If the relaying path has non-zero packet delays, this method also updates the client on the
    /// target chain with the appropriate headers.
    fn schedule_operational_data(
        &mut self,
        mut od: OperationalData<ChainA, ChainB>,
    ) -> Result<(), LinkError> {
        if od.is_empty_batch() {
            info!(
                "[{}] ignoring operational data for {} because it has no messages",
                self,
                od.target()
            );
            return Ok(());
        }

        info!(
            "[{}] scheduling op. data with {} msg(s) for {} (height {})",
            self,
            od.batch_len(),
            od.target(),
            od.untagged_height().increment(), // increment for easier correlation with the client logs
        );

        match od {
            OperationalData::Src(data) => {
                // Update clients ahead of scheduling the operational data, if the delays are non-zero.
                if !self.zero_delay() {
                    let height = data.proofs_height.map(|h| h.increment());
                    self.update_client_src(height)?;
                }

                data.scheduled_time = Instant::now();
                self.src_operational_data.push_back(data);
            }
            OperationalData::Dst(data) => {
                if !self.zero_delay() {
                    let height = data.proofs_height.map(|h| h.increment());
                    self.update_client_dst(height)?;
                }

                data.scheduled_time = Instant::now();
                self.dst_operational_data.push_back(data);
            }
        }

        Ok(())
    }

    /// Pulls out the operational elements with elapsed delay period and that can
    /// now be processed. Does not block: if no OD fulfilled the delay period (or none is
    /// scheduled), returns immediately with `vec![]`.
    fn try_fetch_scheduled_operational_data(
        &mut self,
    ) -> (
        Vec<SrcOperationPayload<ChainA, ChainB>>,
        Vec<DstOperationPayload<ChainA, ChainB>>,
    ) {
        fn extract<T>(queue: &mut VecDeque<T>, pred: impl Fn(&T) -> bool) -> Vec<T> {
            let mut unextracted = VecDeque::new();
            let mut extracted = Vec::new();

            for e in queue.drain(0..) {
                if pred(&e) {
                    extracted.push(e);
                } else {
                    unextracted.push_back(e);
                }
            }

            *queue = unextracted;
            extracted
        }

        let connection_delay = self.channel.connection_delay;

        let src_ods = extract(&mut self.src_operational_data, |op| {
            op.scheduled_time.elapsed() > connection_delay
        });

        let dst_ods = extract(&mut self.dst_operational_data, |op| {
            op.scheduled_time.elapsed() > connection_delay
        });

        (src_ods, dst_ods)
    }

    /// Fetches an operational data that has fulfilled its predefined delay period. May _block_
    /// waiting for the delay period to pass.
    /// Returns `None` if there is no operational data scheduled.
    pub(crate) fn fetch_scheduled_operational_data(
        &mut self,
    ) -> Option<OperationalData<ChainA, ChainB>> {
        let odata = self
            .src_operational_data
            .pop_front()
            .map(OperationalData::Src)
            .or_else(|| {
                self.dst_operational_data
                    .pop_front()
                    .map(OperationalData::Dst)
            });

        if let Some(odata) = odata {
            // Check if the delay period did not completely elapse
            let delay_left = self
                .channel
                .connection_delay
                .checked_sub(odata.scheduled_time().elapsed());

            match delay_left {
                None => info!(
                    "[{}] ready to fetch a scheduled op. data with batch of size {} targeting {}",
                    self,
                    odata.batch_len(),
                    odata.target(),
                ),
                Some(delay_left) => {
                    info!(
                        "[{}] waiting ({:?} left) for a scheduled op. data with batch of size {} targeting {}",
                        self,
                        delay_left,
                        odata.batch_len(),
                        odata.target(),
                    );

                    // Wait until the delay period passes
                    thread::sleep(delay_left);
                }
            }

            Some(odata)
        } else {
            None
        }
    }

    fn restore_src_client(&self) -> ForeignClient<ChainA, ChainB> {
        ForeignClient::restore(
            self.src_client_id().clone(),
            self.src_chain().clone(),
            self.dst_chain().clone(),
        )
    }

    fn restore_dst_client(&self) -> ForeignClient<ChainB, ChainA> {
        ForeignClient::restore(
            self.dst_client_id().clone(),
            self.dst_chain().clone(),
            self.src_chain().clone(),
        )
    }
}

impl<ChainA, ChainB> fmt::Display for RelayPath<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let channel_id = self
            .src_channel_id()
            .map(|id| id.untag().to_string())
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
