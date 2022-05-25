use alloc::collections::BTreeMap as HashMap;
use alloc::collections::VecDeque;
use std::ops::Sub;
use std::time::{Duration, Instant};

use ibc_proto::google::protobuf::Any;
use itertools::Itertools;
use tracing::{debug, error, info, span, trace, warn, Level};

use crate::chain::counterparty::unreceived_acknowledgements;
use crate::chain::counterparty::unreceived_packets;
use crate::chain::handle::ChainHandle;
use crate::chain::requests::QueryChannelRequest;
use crate::chain::requests::QueryHostConsensusStateRequest;
use crate::chain::requests::QueryNextSequenceReceiveRequest;
use crate::chain::requests::QueryUnreceivedAcksRequest;
use crate::chain::requests::QueryUnreceivedPacketsRequest;
use crate::chain::tracking::TrackedMsgs;
use crate::chain::tracking::TrackingId;
use crate::chain::ChainStatus;
use crate::channel::error::ChannelError;
use crate::channel::Channel;
use crate::event::monitor::EventBatch;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::link::error::{self, LinkError};
use crate::link::operational_data::{
    OperationalData, OperationalDataTarget, TrackedEvents, TransitMessage,
};
use crate::link::packet_events::query_packet_events_with;
use crate::link::packet_events::query_send_packet_events;
use crate::link::packet_events::query_write_ack_events;
use crate::link::pending::PendingTxs;
use crate::link::relay_sender::{AsyncReply, SubmitReply};
use crate::link::relay_summary::RelaySummary;
use crate::link::{pending, relay_sender};
use crate::path::PathIdentifiers;
use crate::telemetry;
use crate::util::queue::Queue;
use ibc::{
    core::{
        ics02_client::{
            client_consensus::QueryClientEventRequest,
            events::ClientMisbehaviour as ClientMisbehaviourEvent,
            events::UpdateClient as UpdateClientEvent,
        },
        ics04_channel::{
            channel::{ChannelEnd, Order, State as ChannelState},
            events::{SendPacket, WriteAcknowledgement},
            msgs::{
                acknowledgement::MsgAcknowledgement, chan_close_confirm::MsgChannelCloseConfirm,
                recv_packet::MsgRecvPacket, timeout::MsgTimeout,
                timeout_on_close::MsgTimeoutOnClose,
            },
            packet::{Packet, PacketMsgType},
        },
        ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
    },
    events::{IbcEvent, PrettyEvents, WithBlockDataType},
    query::QueryTxRequest,
    signer::Signer,
    timestamp::Timestamp,
    tx_msg::Msg,
    Height,
};

const MAX_RETRIES: usize = 5;

/// Whether or not to resubmit packets when pending transactions
/// fail to process within the given timeout duration.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Resubmit {
    Yes,
    No,
}

impl Resubmit {
    /// Packet resubmission is enabled when the clear interval for packets is 0. Otherwise,
    /// when the packet clear interval is > 0, the relayer will periodically clear unsent packets
    /// such that resubmitting packets is not necessary.
    pub fn from_clear_interval(clear_interval: u64) -> Self {
        if clear_interval == 0 {
            Self::Yes
        } else {
            Self::No
        }
    }
}

pub struct RelayPath<ChainA: ChainHandle, ChainB: ChainHandle> {
    channel: Channel<ChainA, ChainB>,

    pub(crate) path_id: PathIdentifiers,

    // Operational data, targeting both the source and destination chain.
    // These vectors of operational data are ordered decreasingly by
    // their age, with element at position `0` being the oldest.
    // The operational data targeting the source chain comprises
    // mostly timeout packet messages.
    // The operational data targeting the destination chain
    // comprises mostly RecvPacket and Ack msgs.
    pub(crate) src_operational_data: Queue<OperationalData>,
    pub(crate) dst_operational_data: Queue<OperationalData>,

    // Toggle for the transaction confirmation mechanism.
    confirm_txes: bool,

    // Stores pending (i.e., unconfirmed) operational data.
    // The relaying path periodically tries to confirm these pending
    // transactions if [`confirm_txes`] is true.
    pending_txs_src: PendingTxs<ChainA>,
    pending_txs_dst: PendingTxs<ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> RelayPath<ChainA, ChainB> {
    pub fn new(
        channel: Channel<ChainA, ChainB>,
        with_tx_confirmation: bool,
    ) -> Result<Self, LinkError> {
        let src_chain = channel.src_chain().clone();
        let dst_chain = channel.dst_chain().clone();

        let src_chain_id = src_chain.id();
        let dst_chain_id = dst_chain.id();

        let src_channel_id = *channel
            .src_channel_id()
            .ok_or_else(|| LinkError::missing_channel_id(src_chain.id()))?;

        let dst_channel_id = *channel
            .dst_channel_id()
            .ok_or_else(|| LinkError::missing_channel_id(dst_chain.id()))?;

        let src_port_id = channel.src_port_id().clone();
        let dst_port_id = channel.dst_port_id().clone();

        let path = PathIdentifiers {
            port_id: dst_port_id.clone(),
            channel_id: dst_channel_id,
            counterparty_port_id: src_port_id.clone(),
            counterparty_channel_id: src_channel_id,
        };

        Ok(Self {
            channel,

            path_id: path,

            src_operational_data: Queue::new(),
            dst_operational_data: Queue::new(),

            confirm_txes: with_tx_confirmation,
            pending_txs_src: PendingTxs::new(src_chain, src_channel_id, src_port_id, dst_chain_id),
            pending_txs_dst: PendingTxs::new(dst_chain, dst_channel_id, dst_port_id, src_chain_id),
        })
    }

    pub fn src_chain(&self) -> &ChainA {
        self.channel.src_chain()
    }

    pub fn dst_chain(&self) -> &ChainB {
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
        &self.path_id.counterparty_port_id
    }

    pub fn dst_port_id(&self) -> &PortId {
        &self.path_id.port_id
    }

    pub fn src_channel_id(&self) -> &ChannelId {
        &self.path_id.counterparty_channel_id
    }

    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.path_id.channel_id
    }

    pub fn channel(&self) -> &Channel<ChainA, ChainB> {
        &self.channel
    }

    fn src_channel(&self, height: Height) -> Result<ChannelEnd, LinkError> {
        self.src_chain()
            .query_channel(QueryChannelRequest {
                port_id: self.src_port_id().clone(),
                channel_id: *self.src_channel_id(),
                height,
            })
            .map_err(|e| LinkError::channel(ChannelError::query(self.src_chain().id(), e)))
    }

    fn dst_channel(&self, height: Height) -> Result<ChannelEnd, LinkError> {
        self.dst_chain()
            .query_channel(QueryChannelRequest {
                port_id: self.dst_port_id().clone(),
                channel_id: *self.dst_channel_id(),
                height,
            })
            .map_err(|e| LinkError::channel(ChannelError::query(self.dst_chain().id(), e)))
    }

    fn src_signer(&self) -> Result<Signer, LinkError> {
        self.src_chain()
            .get_signer()
            .map_err(|e| LinkError::signer(self.src_chain().id(), e))
    }

    fn dst_signer(&self) -> Result<Signer, LinkError> {
        self.dst_chain()
            .get_signer()
            .map_err(|e| LinkError::signer(self.dst_chain().id(), e))
    }

    pub(crate) fn src_latest_height(&self) -> Result<Height, LinkError> {
        self.src_chain()
            .query_latest_height()
            .map_err(|e| LinkError::query(self.src_chain().id(), e))
    }

    pub(crate) fn dst_latest_height(&self) -> Result<Height, LinkError> {
        self.dst_chain()
            .query_latest_height()
            .map_err(|e| LinkError::query(self.dst_chain().id(), e))
    }

    fn src_time_at_height(&self, height: Height) -> Result<Instant, LinkError> {
        Self::chain_time_at_height(self.src_chain(), height)
    }

    fn dst_time_at_height(&self, height: Height) -> Result<Instant, LinkError> {
        Self::chain_time_at_height(self.dst_chain(), height)
    }

    pub(crate) fn src_time_latest(&self) -> Result<Instant, LinkError> {
        let elapsed = Timestamp::now()
            .duration_since(
                &self
                    .src_chain()
                    .query_application_status()
                    .unwrap()
                    .timestamp,
            )
            .unwrap_or_default();

        Ok(Instant::now().sub(elapsed))
    }

    pub(crate) fn dst_time_latest(&self) -> Result<Instant, LinkError> {
        let elapsed = Timestamp::now()
            .duration_since(
                &self
                    .dst_chain()
                    .query_application_status()
                    .unwrap()
                    .timestamp,
            )
            .unwrap_or_default();

        Ok(Instant::now().sub(elapsed))
    }

    pub(crate) fn src_max_block_time(&self) -> Result<Duration, LinkError> {
        // TODO(hu55a1n1): Ideally, we should get the `max_expected_time_per_block` using the
        // `/genesis` endpoint once it is working in tendermint-rs.
        Ok(self
            .src_chain()
            .config()
            .map_err(LinkError::relayer)?
            .max_block_time)
    }

    pub(crate) fn dst_max_block_time(&self) -> Result<Duration, LinkError> {
        Ok(self
            .dst_chain()
            .config()
            .map_err(LinkError::relayer)?
            .max_block_time)
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
            .map_err(LinkError::client)
    }

    pub fn build_update_client_on_src(&self, height: Height) -> Result<Vec<Any>, LinkError> {
        let client = self.restore_src_client();
        client
            .build_update_client(height)
            .map_err(LinkError::client)
    }

    fn build_chan_close_confirm_from_event(&self, event: &IbcEvent) -> Result<Any, LinkError> {
        let src_channel_id = self.src_channel_id();
        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, event.height())
            .map_err(|e| LinkError::channel(ChannelError::channel_proof(e)))?;

        // Build the domain type message
        let new_msg = MsgChannelCloseConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: *self.dst_channel_id(),
            proofs,
            signer: self.dst_signer()?,
        };

        Ok(new_msg.to_any())
    }

    /// Determines if the events received are relevant and should be processed.
    /// Only events for a port/channel matching one of the channel ends should be processed.
    fn filter_relaying_events(
        &self,
        events: Vec<IbcEvent>,
        tracking_id: TrackingId,
    ) -> TrackedEvents {
        let src_channel_id = self.src_channel_id();

        let mut result = vec![];

        for event in events.into_iter() {
            match &event {
                IbcEvent::SendPacket(send_packet_ev) => {
                    if src_channel_id == send_packet_ev.src_channel_id()
                        && self.src_port_id() == send_packet_ev.src_port_id()
                    {
                        result.push(event);
                    }
                }
                IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                    if src_channel_id == write_ack_ev.dst_channel_id()
                        && self.src_port_id() == write_ack_ev.dst_port_id()
                    {
                        result.push(event);
                    }
                }
                IbcEvent::CloseInitChannel(chan_close_ev) => {
                    if src_channel_id == chan_close_ev.channel_id()
                        && self.src_port_id() == chan_close_ev.port_id()
                    {
                        result.push(event);
                    }
                }
                IbcEvent::TimeoutPacket(timeout_ev) => {
                    if src_channel_id == timeout_ev.src_channel_id()
                        && self.channel.src_port_id() == timeout_ev.src_port_id()
                    {
                        result.push(event);
                    }
                }
                _ => {}
            }
        }

        // Transform into `TrackedEvents`
        TrackedEvents::new(result, tracking_id)
    }

    fn relay_pending_packets(&self, height: Option<Height>) -> Result<(), LinkError> {
        let tracking_id = TrackingId::new_static("relay pending packets");

        for i in 1..=MAX_RETRIES {
            let cleared = self
                .schedule_recv_packet_and_timeout_msgs(height, tracking_id)
                .and_then(|()| self.schedule_packet_ack_msgs(height, tracking_id));

            match cleared {
                Ok(()) => return Ok(()),
                Err(e) => error!(
                    "failed to clear packets, retry {}/{}: {}",
                    i, MAX_RETRIES, e
                ),
            }
        }

        Err(LinkError::old_packet_clearing_failed())
    }

    /// Clears any packets that were sent before `height`.
    pub fn schedule_packet_clearing(&self, height: Option<Height>) -> Result<(), LinkError> {
        let span = span!(Level::DEBUG, "clear");
        let _enter = span.enter();

        let clear_height = height
            .map(|h| h.decrement().map_err(|e| LinkError::decrement_height(h, e)))
            .transpose()?;

        self.relay_pending_packets(clear_height)?;

        debug!(height = ?clear_height, "done scheduling");
        Ok(())
    }

    /// Generate & schedule operational data from the input `batch` of IBC events.
    pub fn update_schedule(&self, batch: EventBatch) -> Result<(), LinkError> {
        // Collect relevant events from the incoming batch & adjust their height.
        let events = self.filter_relaying_events(batch.events, batch.tracking_id);

        // Transform the events into operational data items
        self.events_to_operational_data(events)
    }

    /// Produces and schedules operational data for this relaying path based on the input events.
    pub(crate) fn events_to_operational_data(
        &self,
        events: TrackedEvents,
    ) -> Result<(), LinkError> {
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
        events: TrackedEvents,
    ) -> Result<(Option<OperationalData>, Option<OperationalData>), LinkError> {
        let span = span!(Level::DEBUG, "generate", id = %events.tracking_id());
        let _enter = span.enter();

        let input = events.events();
        let src_height = match input.get(0) {
            None => return Ok((None, None)),
            Some(ev) => ev.height(),
        };

        let dst_latest_info = self
            .dst_chain()
            .query_application_status()
            .map_err(|e| LinkError::query(self.src_chain().id(), e))?;

        let dst_latest_height = dst_latest_info.height;

        // Operational data targeting the source chain (e.g., Timeout packets)
        let mut src_od = OperationalData::new(
            dst_latest_height,
            OperationalDataTarget::Source,
            events.tracking_id(),
            self.channel.connection_delay,
        );

        // Operational data targeting the destination chain (e.g., SendPacket messages)
        let mut dst_od = OperationalData::new(
            src_height,
            OperationalDataTarget::Destination,
            events.tracking_id(),
            self.channel.connection_delay,
        );

        for event in input {
            trace!("processing event: {}", event);
            let (dst_msg, src_msg) = match event {
                IbcEvent::CloseInitChannel(_) => {
                    (Some(self.build_chan_close_confirm_from_event(event)?), None)
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
                        (Some(self.build_chan_close_confirm_from_event(event)?), None)
                    } else {
                        (None, None)
                    }
                }
                IbcEvent::SendPacket(ref send_packet_ev) => {
                    if self.send_packet_event_handled(send_packet_ev)? {
                        debug!("{} already handled", send_packet_ev);
                        (None, None)
                    } else {
                        self.build_recv_or_timeout_from_send_packet_event(
                            send_packet_ev,
                            &dst_latest_info,
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
                        debug!("{} already handled", write_ack_ev);
                        (None, None)
                    } else {
                        (self.build_ack_from_recv_event(write_ack_ev)?, None)
                    }
                }
                _ => (None, None),
            };

            // Collect messages to be sent to the destination chain (e.g., RecvPacket)
            if let Some(msg) = dst_msg {
                debug!("{} from {}", msg.type_url, event);
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
                    debug!("{} from {}", msg.type_url, event);
                    src_od.batch.push(TransitMessage {
                        event: event.clone(),
                        msg,
                    });
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

    /// Relays an [`OperationalData`] using a specific
    /// sender, which implements [`relay_sender::Submit`].
    pub(crate) fn relay_from_operational_data<S: relay_sender::Submit>(
        &self,
        initial_od: OperationalData,
    ) -> Result<S::Reply, LinkError> {
        // We will operate on potentially different operational data if the initial one fails.
        let _span = span!(Level::INFO, "relay", odata = %initial_od.info()).entered();

        let mut odata = initial_od;

        for i in 0..MAX_RETRIES {
            debug!("[try {}/{}]", i + 1, MAX_RETRIES);

            // Consume the operational data by attempting to send its messages
            match self.send_from_operational_data::<S>(&odata) {
                Ok(reply) => {
                    // Done with this op. data
                    info!("success");

                    return Ok(reply);
                }
                Err(LinkError(error::LinkErrorDetail::Send(e), _)) => {
                    // This error means we could retry
                    error!("error {}", e.event);
                    if i + 1 == MAX_RETRIES {
                        error!("{}/{} retries exhausted. giving up", i + 1, MAX_RETRIES)
                    } else {
                        // If we haven't exhausted all retries, regenerate the op. data & retry
                        match self.regenerate_operational_data(odata.clone()) {
                            None => return Ok(S::Reply::empty()), // Nothing to retry
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

        Ok(S::Reply::empty())
    }

    /// Generates fresh operational data for a tx given the initial operational data
    /// that failed to send.
    ///
    /// Return value:
    ///   - `Some(..)`: a new operational data from which to retry sending,
    ///   - `None`: all the events in the initial operational data were exhausted (i.e., turned
    ///   into timeouts), so there is nothing to retry.
    ///
    /// Side effects: may schedule a new operational data targeting the source chain, comprising
    /// new timeout messages.
    pub(crate) fn regenerate_operational_data(
        &self,
        initial_odata: OperationalData,
    ) -> Option<OperationalData> {
        let op_info = initial_odata.info();

        warn!(
            "failed. Regenerate operational data from {} events",
            op_info.batch_len()
        );

        // Retry by re-generating the operational data using the initial events
        let (src_opt, dst_opt) = match self.generate_operational_data(initial_odata.into_events()) {
            Ok(new_operational_data) => new_operational_data,
            Err(e) => {
                error!(
                    "failed to regenerate operational data from initial data: {} \
                    with error {}, discarding this op. data",
                    op_info, e
                );
                return None;
            } // Cannot retry, contain the error by reporting a None
        };

        if let Some(src_od) = src_opt {
            if src_od.target == op_info.target() {
                // Our target is the _source_ chain, retry these messages
                info!(odata = %src_od.info(), "will retry");
                return Some(src_od);
            } else {
                // Our target is the _destination_ chain, the data in `src_od` contains
                // potentially new timeout messages that have to be handled separately.
                if let Err(e) = self.schedule_operational_data(src_od) {
                    error!(
                        "failed to schedule newly-generated operational data from \
                        initial data: {} with error {}, discarding this op. data",
                        op_info, e
                    );
                    return None;
                }
            }
        }

        if let Some(dst_od) = dst_opt {
            if dst_od.target == op_info.target() {
                // Our target is the _destination_ chain, retry these messages
                info!(odata = %dst_od.info(), "will retry");
                return Some(dst_od);
            } else {
                // Our target is the _source_ chain, but `dst_od` has new messages
                // intended for the destination chain, this should never be the case
                error!(
                    "generated new messages for destination chain while handling \
                    failed events targeting the source chain!",
                );
            }
        } else {
            // There is no message intended for the destination chain
            if op_info.target() == OperationalDataTarget::Destination {
                info!("exhausted all events from this operational data");
                return None;
            }
        }

        None
    }

    /// Sends a transaction based on the [`OperationalData`] to
    /// the corresponding target chain.
    ///
    /// Returns the appropriate reply associated with the given
    /// [`relay_sender::Submit`]. The reply consists of either the tx
    /// hashes generated by the target chain, if [`Async`] sender,
    /// or the ibc events, if the sender is [`Sync`].
    ///
    /// Propagates any encountered errors.
    fn send_from_operational_data<S: relay_sender::Submit>(
        &self,
        odata: &OperationalData,
    ) -> Result<S::Reply, LinkError> {
        if odata.batch.is_empty() {
            error!("ignoring empty operational data!");
            return Ok(S::Reply::empty());
        }

        let msgs = odata.assemble_msgs(self)?;

        telemetry!({
            let (chain, counterparty, channel_id, port_id) = self.target_info(odata.target);

            ibc_telemetry::global().tx_submitted(
                msgs.tracking_id,
                &chain,
                channel_id,
                port_id,
                &counterparty,
            );
        });

        match odata.target {
            OperationalDataTarget::Source => S::submit(self.src_chain(), msgs),
            OperationalDataTarget::Destination => S::submit(self.dst_chain(), msgs),
        }
    }

    fn enqueue_pending_tx(&self, reply: AsyncReply, odata: OperationalData) {
        if !self.confirm_txes {
            return;
        }

        match odata.target {
            OperationalDataTarget::Source => {
                self.pending_txs_src.insert_new_pending_tx(reply, odata);
            }
            OperationalDataTarget::Destination => {
                self.pending_txs_dst.insert_new_pending_tx(reply, odata);
            }
        }
    }

    /// Checks if a sent packet has been received on destination.
    fn send_packet_received_on_dst(&self, packet: &Packet) -> Result<bool, LinkError> {
        let unreceived_packet = self
            .dst_chain()
            .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                port_id: self.dst_port_id().clone(),
                channel_id: *self.dst_channel_id(),
                packet_commitment_sequences: vec![packet.sequence],
            })
            .map_err(LinkError::relayer)?;

        Ok(unreceived_packet.is_empty())
    }

    /// Checks if a packet commitment has been cleared on source.
    /// The packet commitment is cleared when either an acknowledgment or a timeout is received on source.
    fn send_packet_commitment_cleared_on_src(&self, packet: &Packet) -> Result<bool, LinkError> {
        let (bytes, _) = self
            .src_chain()
            .build_packet_proofs(
                PacketMsgType::Recv,
                self.src_port_id(),
                self.src_channel_id(),
                packet.sequence,
                Height::zero(),
            )
            .map_err(LinkError::relayer)?;

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
        let unreceived_ack = self
            .dst_chain()
            .query_unreceived_acknowledgement(QueryUnreceivedAcksRequest {
                port_id: self.dst_port_id().clone(),
                channel_id: *self.dst_channel_id(),
                packet_ack_sequences: vec![packet.sequence],
            })
            .map_err(LinkError::relayer)?;

        Ok(unreceived_ack.is_empty())
    }

    /// Checks if a receive packet event has already been handled (e.g. by another relayer).
    fn write_ack_event_handled(&self, rp: &WriteAcknowledgement) -> Result<bool, LinkError> {
        self.recv_packet_acknowledged_on_src(&rp.packet)
    }

    /// Returns the `processed_height` for the consensus state at specified height
    fn update_height(
        chain: &impl ChainHandle,
        client_id: ClientId,
        consensus_height: Height,
    ) -> Result<Height, LinkError> {
        let events = chain
            .query_txs(QueryTxRequest::Client(QueryClientEventRequest {
                height: Height::zero(),
                event_id: WithBlockDataType::UpdateClient,
                client_id,
                consensus_height,
            }))
            .map_err(|e| LinkError::query(chain.id(), e))?;

        // The handler may treat redundant updates as no-ops and emit `UpdateClient` events for them
        // but the `processed_height` is the height at which the first `UpdateClient` event for this
        // consensus state/height was emitted. We expect that these events are received in the exact
        // same order in which they were emitted.
        match events.first() {
            Some(IbcEvent::UpdateClient(event)) => Ok(event.height()),
            Some(event) => Err(LinkError::unexpected_event(event.clone())),
            None => Err(LinkError::unexpected_event(IbcEvent::default())),
        }
    }

    /// Loops over `tx_events` and returns a tuple of optional events where the first element is a
    /// `ChainError` variant, the second one is an `UpdateClient` variant and the third one is a
    /// `ClientMisbehaviour` variant. This function is essentially just an `Iterator::find()` for
    /// multiple variants with a single pass.
    #[inline]
    fn event_per_type(
        mut tx_events: Vec<IbcEvent>,
    ) -> (
        Option<IbcEvent>,
        Option<UpdateClientEvent>,
        Option<ClientMisbehaviourEvent>,
    ) {
        let mut error = None;
        let mut update = None;
        let mut misbehaviour = None;

        while let Some(event) = tx_events.pop() {
            match event {
                IbcEvent::ChainError(_) => error = Some(event),
                IbcEvent::UpdateClient(event) => update = Some(event),
                IbcEvent::ClientMisbehaviour(event) => misbehaviour = Some(event),
                _ => {}
            }
        }

        (error, update, misbehaviour)
    }

    /// Returns an instant (in the past) that corresponds to the block timestamp of the chain at
    /// specified height (relative to the relayer's current time). If the timestamp is in the future
    /// wrt the relayer's current time, we simply return the current relayer time.
    fn chain_time_at_height(
        chain: &impl ChainHandle,
        height: Height,
    ) -> Result<Instant, LinkError> {
        let chain_time = chain
            .query_host_consensus_state(QueryHostConsensusStateRequest { height })
            .map_err(LinkError::relayer)?
            .timestamp();
        let duration = Timestamp::now()
            .duration_since(&chain_time)
            .unwrap_or_default();
        Ok(Instant::now().sub(duration))
    }

    /// Handles updating the client on the destination chain
    /// Returns the height at which the client update was processed
    fn update_client_dst(
        &self,
        src_chain_height: Height,
        tracking_id: TrackingId,
    ) -> Result<Height, LinkError> {
        self.do_update_client_dst(src_chain_height, tracking_id, MAX_RETRIES)
    }

    /// Perform actual update_client_dst with retries.
    ///
    /// Note that the retry is only performed in the case when there
    /// is a ChainError event. It would return error immediately if
    /// there are other errors returned from calls such as
    /// build_update_client_on_dst.
    fn do_update_client_dst(
        &self,
        src_chain_height: Height,
        tracking_id: TrackingId,
        retries_left: usize,
    ) -> Result<Height, LinkError> {
        info!( "sending update_client to client hosted on source chain for height {} (retries left: {})", src_chain_height, retries_left );

        let dst_update = self.build_update_client_on_dst(src_chain_height)?;
        let tm = TrackedMsgs::new(dst_update, tracking_id);
        let dst_tx_events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(LinkError::relayer)?;

        info!("result: {}", PrettyEvents(&dst_tx_events));

        let (error, update, misbehaviour) = Self::event_per_type(dst_tx_events);
        match (error, update, misbehaviour) {
            // All updates were successful, no errors and no misbehaviour.
            (None, Some(update_event), None) => Ok(update_event.height()),
            (Some(chain_error), _, _) => {
                // Atleast one chain-error so retry if possible.
                if retries_left == 0 {
                    Err(LinkError::client(ForeignClientError::chain_error_event(
                        self.dst_chain().id(),
                        chain_error,
                    )))
                } else {
                    self.do_update_client_dst(src_chain_height, tracking_id, retries_left - 1)
                }
            }
            (None, None, None) => {
                // `tm` was empty and update wasn't required
                match Self::update_height(
                    self.dst_chain(),
                    self.dst_client_id().clone(),
                    src_chain_height,
                ) {
                    Ok(update_height) => Ok(update_height),
                    Err(_) if retries_left > 0 => {
                        self.do_update_client_dst(src_chain_height, tracking_id, retries_left - 1)
                    }
                    _ => Err(LinkError::update_client_failed()),
                }
            }
            // Atleast one misbehaviour event, so don't retry.
            (_, _, Some(_misbehaviour)) => Err(LinkError::update_client_failed()),
        }
    }

    /// Handles updating the client on the source chain
    /// Returns the height at which the client update was processed
    fn update_client_src(
        &self,
        dst_chain_height: Height,
        tracking_id: TrackingId,
    ) -> Result<Height, LinkError> {
        self.do_update_client_src(dst_chain_height, tracking_id, MAX_RETRIES)
    }

    /// Perform actual update_client_src with retries.
    ///
    /// Note that the retry is only performed in the case when there
    /// is a ChainError event. It would return error immediately if
    /// there are other errors returned from calls such as
    /// build_update_client_on_src.
    fn do_update_client_src(
        &self,
        dst_chain_height: Height,
        tracking_id: TrackingId,
        retries_left: usize,
    ) -> Result<Height, LinkError> {
        info!( "sending update_client to client hosted on source chain for height {} (retries left: {})", dst_chain_height, retries_left );

        let src_update = self.build_update_client_on_src(dst_chain_height)?;
        let tm = TrackedMsgs::new(src_update, tracking_id);
        let src_tx_events = self
            .src_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(LinkError::relayer)?;

        info!("result: {}", PrettyEvents(&src_tx_events));

        let (error, update, misbehaviour) = Self::event_per_type(src_tx_events);
        match (error, update, misbehaviour) {
            // All updates were successful, no errors and no misbehaviour.
            (None, Some(update_event), None) => Ok(update_event.height()),
            (Some(chain_error), _, _) => {
                // Atleast one chain-error so retry if possible.
                if retries_left == 0 {
                    Err(LinkError::client(ForeignClientError::chain_error_event(
                        self.src_chain().id(),
                        chain_error,
                    )))
                } else {
                    self.do_update_client_src(dst_chain_height, tracking_id, retries_left - 1)
                }
            }
            (None, None, None) => {
                // `tm` was empty and update wasn't required
                match Self::update_height(
                    self.src_chain(),
                    self.src_client_id().clone(),
                    dst_chain_height,
                ) {
                    Ok(update_height) => Ok(update_height),
                    Err(_) if retries_left > 0 => {
                        self.do_update_client_src(dst_chain_height, tracking_id, retries_left - 1)
                    }
                    _ => Err(LinkError::update_client_failed()),
                }
            }
            // At least one misbehaviour event, so don't retry.
            (_, _, Some(_misbehaviour)) => Err(LinkError::update_client_failed()),
        }
    }

    /// Schedules the relaying of [`MsgRecvPacket`] and [`MsgTimeout`] messages.
    ///
    /// The optional [`Height`] parameter allows specify a height on the source
    /// chain where to query for packet data. If `None`, the latest available
    /// height on the source chain is used.
    ///
    /// Blocks until _all_ outstanding messages have been scheduled.
    pub fn schedule_recv_packet_and_timeout_msgs(
        &self,
        opt_query_height: Option<Height>,
        tracking_id: TrackingId,
    ) -> Result<(), LinkError> {
        let _span =
            span!(Level::DEBUG, "schedule_recv_packet_and_timeout_msgs", query_height = ?opt_query_height)
                .entered();

        // Pull the s.n. of all packets that the destination chain has not yet received.
        let (sequences, src_response_height) =
            unreceived_packets(self.dst_chain(), self.src_chain(), &self.path_id)
                .map_err(LinkError::supervisor)?;

        let query_height = opt_query_height.unwrap_or(src_response_height);

        // Skip: no relevant events found.
        if sequences.is_empty() {
            return Ok(());
        }

        debug!(
            "sequences of unreceived packets to send out to {} of the ones with commitments on {}: {} (first 10 shown here; total={})",
            self.dst_chain().id(),
            self.src_chain().id(),
            sequences.iter().take(10).format(", "), sequences.len()
        );

        // Chunk-up the list of sequence nrs. into smaller parts,
        // and schedule operational data incrementally across each chunk.
        for events_chunk in query_packet_events_with(
            &sequences,
            query_height,
            self.src_chain(),
            &self.path_id,
            query_send_packet_events,
        ) {
            self.events_to_operational_data(TrackedEvents::new(events_chunk, tracking_id))?;
        }

        Ok(())
    }

    /// Schedules the relaying of [`MsgAcknowledgement`] messages.
    ///
    /// The `opt_query_height` parameter allows to optionally use a specific height on the source
    /// chain where to query for packet data. If `None`, the latest available height on the source
    /// chain is used.
    pub fn schedule_packet_ack_msgs(
        &self,
        opt_query_height: Option<Height>,
        tracking_id: TrackingId,
    ) -> Result<(), LinkError> {
        let _span = span!(Level::DEBUG, "build_packet_ack_msgs", h = ?opt_query_height).entered();

        let (sequences, src_response_height) =
            unreceived_acknowledgements(self.dst_chain(), self.src_chain(), &self.path_id)
                .map_err(LinkError::supervisor)?;

        let query_height = opt_query_height.unwrap_or(src_response_height);

        // Skip: no relevant events found.
        if sequences.is_empty() {
            return Ok(());
        }

        debug!(
            "seq. nrs. of ack packets to send out to {} of the ones with acknowledgments on {}: {} (first 10 shown here; total={})",
            self.dst_chain().id(),
            self.src_chain().id(),
            sequences.iter().take(10).format(", "), sequences.len()
        );

        // Incrementally process all the available sequence numbers in chunks
        for events_chunk in query_packet_events_with(
            &sequences,
            query_height,
            self.src_chain(),
            &self.path_id,
            query_write_ack_events,
        ) {
            self.events_to_operational_data(TrackedEvents::new(events_chunk, tracking_id))?;
        }

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
            .map_err(|e| LinkError::packet_proofs_constructor(self.src_chain().id(), e))?;

        let msg = MsgRecvPacket::new(packet.clone(), proofs.clone(), self.dst_signer()?);

        trace!(
            "built recv_packet msg {}, proofs at height {}",
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
            .map_err(|e| LinkError::packet_proofs_constructor(self.src_chain().id(), e))?;

        let msg = MsgAcknowledgement::new(
            packet,
            event.ack.clone().into(),
            proofs.clone(),
            self.dst_signer()?,
        );

        trace!(
            "built acknowledgment msg {}, proofs at height {}",
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
        let dst_channel_id = self.dst_channel_id();

        debug!("build timeout for channel");
        let (packet_type, next_sequence_received) = if self.ordered_channel() {
            let next_seq = self
                .dst_chain()
                .query_next_sequence_receive(QueryNextSequenceReceiveRequest {
                    port_id: self.dst_port_id().clone(),
                    channel_id: *dst_channel_id,
                })
                .map_err(|e| LinkError::query(self.dst_chain().id(), e))?;
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
            .map_err(|e| LinkError::packet_proofs_constructor(self.dst_chain().id(), e))?;

        let msg = MsgTimeout::new(
            packet.clone(),
            next_sequence_received,
            proofs.clone(),
            self.src_signer()?,
        );

        trace!(
            "built timeout msg {}, proofs at height {}",
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
            .map_err(|e| LinkError::packet_proofs_constructor(self.dst_chain().id(), e))?;

        let msg = MsgTimeoutOnClose::new(
            packet.clone(),
            packet.sequence,
            proofs.clone(),
            self.src_signer()?,
        );

        trace!(
            "built timeout on close msg {}, proofs at height {}",
            msg.packet,
            proofs.height()
        );

        Ok(Some(msg.to_any()))
    }

    fn build_timeout_from_send_packet_event(
        &self,
        event: &SendPacket,
        dst_info: &ChainStatus,
    ) -> Result<Option<Any>, LinkError> {
        let packet = event.packet.clone();
        if self
            .dst_channel(dst_info.height)?
            .state_matches(&ChannelState::Closed)
        {
            Ok(self.build_timeout_on_close_packet(&event.packet, dst_info.height)?)
        } else if packet.timed_out(&dst_info.timestamp, dst_info.height) {
            Ok(self.build_timeout_packet(&event.packet, dst_info.height)?)
        } else {
            Ok(None)
        }
    }

    fn build_recv_or_timeout_from_send_packet_event(
        &self,
        event: &SendPacket,
        dst_info: &ChainStatus,
    ) -> Result<(Option<Any>, Option<Any>), LinkError> {
        let timeout = self.build_timeout_from_send_packet_event(event, dst_info)?;
        if timeout.is_some() {
            Ok((None, timeout))
        } else {
            Ok((self.build_recv_packet(&event.packet, event.height)?, None))
        }
    }

    /// Checks if there are any operational data items ready,
    /// and if so performs the relaying of corresponding packets
    /// to the target chain.
    ///
    /// This method performs relaying using the asynchronous sender.
    /// Retains the operational data as pending, and associates it
    /// with one or more transaction hash(es).
    pub fn execute_schedule(&self) -> Result<(), LinkError> {
        let (src_ods, dst_ods) = self.try_fetch_scheduled_operational_data()?;

        for od in dst_ods {
            let reply =
                self.relay_from_operational_data::<relay_sender::AsyncSender>(od.clone())?;

            self.enqueue_pending_tx(reply, od);
        }

        for od in src_ods {
            let reply =
                self.relay_from_operational_data::<relay_sender::AsyncSender>(od.clone())?;
            self.enqueue_pending_tx(reply, od);
        }

        Ok(())
    }

    /// Kicks off the process of relaying pending txs to the source and destination chains.
    ///
    /// See [`Resubmit::from_clear_interval`] for more info about the `resubmit` parameter.
    pub fn process_pending_txs(&self, resubmit: Resubmit) -> RelaySummary {
        if !self.confirm_txes {
            return RelaySummary::empty();
        }

        let mut summary_src = self.process_pending_txs_src(resubmit).unwrap_or_else(|e| {
            error!("error processing pending events in source chain: {}", e);
            RelaySummary::empty()
        });

        let summary_dst = self.process_pending_txs_dst(resubmit).unwrap_or_else(|e| {
            error!(
                "error processing pending events in destination chain: {}",
                e
            );
            RelaySummary::empty()
        });

        summary_src.extend(summary_dst);
        summary_src
    }

    fn process_pending_txs_src(&self, resubmit: Resubmit) -> Result<RelaySummary, LinkError> {
        let do_resubmit = match resubmit {
            Resubmit::Yes => {
                Some(|odata| self.relay_from_operational_data::<relay_sender::AsyncSender>(odata))
            }
            Resubmit::No => None,
        };

        let res = self
            .pending_txs_src
            .process_pending(pending::TIMEOUT, self, do_resubmit)?
            .unwrap_or_else(RelaySummary::empty);

        Ok(res)
    }

    fn process_pending_txs_dst(&self, resubmit: Resubmit) -> Result<RelaySummary, LinkError> {
        let do_resubmit = match resubmit {
            Resubmit::Yes => {
                Some(|odata| self.relay_from_operational_data::<relay_sender::AsyncSender>(odata))
            }
            Resubmit::No => None,
        };

        let res = self
            .pending_txs_dst
            .process_pending(pending::TIMEOUT, self, do_resubmit)?
            .unwrap_or_else(RelaySummary::empty);

        Ok(res)
    }

    /// Refreshes the scheduled batches.
    /// Verifies if any sendPacket messages timed-out. If so, moves them from destination op. data
    /// to source operational data, and adjusts the events and messages accordingly.
    pub fn refresh_schedule(&self) -> Result<(), LinkError> {
        // Bail fast if no op. data to refresh
        if self.dst_operational_data.is_empty() {
            return Ok(());
        }

        let span = span!(Level::INFO, "refresh");
        let _enter = span.enter();

        let dst_status = self
            .dst_chain()
            .query_application_status()
            .map_err(|e| LinkError::query(self.src_chain().id(), e))?;

        let dst_current_height = dst_status.height;

        // Intermediary data struct to help better manage the transfer from dst. operational data
        // to source operational data.
        let mut all_dst_odata = self.dst_operational_data.clone_vec();

        let mut timed_out: HashMap<usize, OperationalData> = HashMap::default();

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
                            debug!("already handled send packet {}", e);
                        } else if let Some(new_msg) =
                            self.build_timeout_from_send_packet_event(e, &dst_status)?
                        {
                            debug!("found a timed-out msg in the op data {}", odata.info(),);
                            timed_out
                                .entry(odata_pos)
                                .or_insert_with(|| {
                                    OperationalData::new(
                                        dst_current_height,
                                        OperationalDataTarget::Source,
                                        odata.tracking_id,
                                        self.channel.connection_delay,
                                    )
                                })
                                .push(TransitMessage {
                                    event: event.clone(),
                                    msg: new_msg,
                                });
                        } else {
                            // A SendPacket event, but did not time-out yet, retain
                            retain_batch.push(gm.clone());
                        }
                    }
                    IbcEvent::WriteAcknowledgement(e) => {
                        if self.write_ack_event_handled(e)? {
                            debug!("already handled {} write ack ", e);
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

        // Possibly some op. data became empty (if no events were kept).
        // Retain only the non-empty ones.
        all_dst_odata.retain(|o| !o.batch.is_empty());

        // Replace the original operational data with the updated one
        self.dst_operational_data.replace(all_dst_odata);

        // Handle timed-out events
        if timed_out.is_empty() {
            // Nothing timed out in the meantime
            return Ok(());
        }

        // Schedule new operational data targeting the source chain
        for (_, new_od) in timed_out.into_iter() {
            info!(
                "re-scheduling from new timed-out batch of size {}",
                new_od.batch.len()
            );

            self.schedule_operational_data(new_od)?;
        }

        Ok(())
    }

    /// Adds a new operational data item for this relaying path to process later.
    /// If the relaying path has non-zero packet delays, this method also updates the client on the
    /// target chain with the appropriate headers.
    fn schedule_operational_data(&self, mut od: OperationalData) -> Result<(), LinkError> {
        let _span = span!(Level::INFO, "schedule", odata = %od.info()).entered();

        if od.batch.is_empty() {
            info!(
                "ignoring operational data for {} because it has no messages",
                od.target
            );
            return Ok(());
        }

        // Update clients ahead of scheduling the operational data, if the delays are non-zero.
        // If the connection-delay must be taken into account, set the `scheduled_time` to an
        // instant in the past, i.e. when this client update was first processed (`processed_time`)
        let scheduled_time = if od.conn_delay_needed() {
            debug!("connection delay must be taken into account: updating client");
            let target_height = od.proofs_height.increment();
            match od.target {
                OperationalDataTarget::Source => {
                    let update_height = self.update_client_src(target_height, od.tracking_id)?;
                    od.set_update_height(update_height);
                    self.src_time_at_height(update_height)?
                }
                OperationalDataTarget::Destination => {
                    let update_height = self.update_client_dst(target_height, od.tracking_id)?;
                    od.set_update_height(update_height);
                    self.dst_time_at_height(update_height)?
                }
            }
        } else {
            debug!(
                "connection delay need not be taken into account: client update message will be \
            prepended later"
            );
            Instant::now()
        };

        od.set_scheduled_time(scheduled_time);

        match od.target {
            OperationalDataTarget::Source => self.src_operational_data.push_back(od),
            OperationalDataTarget::Destination => self.dst_operational_data.push_back(od),
        };

        Ok(())
    }

    /// Pulls out the operational elements with elapsed delay period and that can
    /// now be processed.
    pub(crate) fn try_fetch_scheduled_operational_data(
        &self,
    ) -> Result<(VecDeque<OperationalData>, VecDeque<OperationalData>), LinkError> {
        // Extracts elements from a Vec when the predicate returns true.
        // The mutable vector is then updated to the remaining unextracted elements.
        fn partition<T>(
            queue: VecDeque<T>,
            pred: impl Fn(&T) -> Result<bool, LinkError>,
        ) -> Result<(VecDeque<T>, VecDeque<T>), LinkError> {
            let mut true_res = VecDeque::new();
            let mut false_res = VecDeque::new();

            for e in queue.into_iter() {
                if pred(&e)? {
                    true_res.push_back(e);
                } else {
                    false_res.push_back(e);
                }
            }

            Ok((true_res, false_res))
        }

        let (elapsed_src_ods, unelapsed_src_ods) =
            partition(self.src_operational_data.take(), |op| {
                op.has_conn_delay_elapsed(
                    &|| self.src_time_latest(),
                    &|| self.src_max_block_time(),
                    &|| self.src_latest_height(),
                )
            })?;

        let (elapsed_dst_ods, unelapsed_dst_ods) =
            partition(self.dst_operational_data.take(), |op| {
                op.has_conn_delay_elapsed(
                    &|| self.dst_time_latest(),
                    &|| self.dst_max_block_time(),
                    &|| self.dst_latest_height(),
                )
            })?;

        self.src_operational_data.replace(unelapsed_src_ods);
        self.dst_operational_data.replace(unelapsed_dst_ods);
        Ok((elapsed_src_ods, elapsed_dst_ods))
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

    // we need fully qualified ChainId to avoid unneeded imports warnings
    #[cfg(feature = "telemetry")]
    fn target_info(
        &self,
        target: OperationalDataTarget,
    ) -> (
        ibc::core::ics24_host::identifier::ChainId, // source chain
        ibc::core::ics24_host::identifier::ChainId, // destination chain
        &ChannelId,
        &PortId,
    ) {
        match target {
            OperationalDataTarget::Source => (
                self.src_chain().id(),
                self.dst_chain().id(),
                self.src_channel_id(),
                self.src_port_id(),
            ),
            OperationalDataTarget::Destination => (
                self.dst_chain().id(),
                self.src_chain().id(),
                self.dst_channel_id(),
                self.dst_port_id(),
            ),
        }
    }
}
