use core::fmt::{Display, Error as FmtError, Formatter};
use std::ops::Add;
use std::time::{Duration, Instant};

use ibc_proto::google::protobuf::Any;
use tracing::{debug, info};

use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::Height;

use crate::chain::handle::ChainHandle;
use crate::chain::requests::IncludeProof;
use crate::chain::requests::QueryClientStateRequest;
use crate::chain::requests::QueryHeight;
use crate::chain::tracking::TrackedMsgs;
use crate::chain::tracking::TrackingId;
use crate::event::IbcEventWithHeight;
use crate::link::error::LinkError;
use crate::link::RelayPath;

/// The chain that the events associated with a piece of [`OperationalData`] are bound for.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OperationalDataTarget {
    /// The chain which generated the events associated with the `OperationalData`.
    Source,
    /// The chain receiving the events associated with the `OperationalData``.
    Destination,
}

impl Display for OperationalDataTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            OperationalDataTarget::Source => write!(f, "Source"),
            OperationalDataTarget::Destination => write!(f, "Destination"),
        }
    }
}

/// A set of [`IbcEventWithHeight`]s that have an associated
/// tracking number to ensure better observability.
pub struct TrackedEvents {
    events: Vec<IbcEventWithHeight>,
    tracking_id: TrackingId,
}

impl TrackedEvents {
    pub fn new(events: Vec<IbcEventWithHeight>, tracking_id: TrackingId) -> Self {
        Self {
            events,
            tracking_id,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    pub fn events(&self) -> &[IbcEventWithHeight] {
        &self.events
    }

    pub fn tracking_id(&self) -> TrackingId {
        self.tracking_id
    }

    pub fn len(&self) -> usize {
        self.events.len()
    }
}

/// A packet message that is prepared for sending
/// to a chain, but has not been sent yet.
///
/// Comprises the proto-encoded packet message,
/// alongside the event which generated it.
#[derive(Clone)]
pub struct TransitMessage {
    pub event_with_height: IbcEventWithHeight,
    pub msg: Any,
}

/// Holds all the necessary information for handling a batch of in-transit messages. This includes
/// an event received from a chain along with any other packets related to the event (i.e.
/// 'receive' or 'timeout' packets) that the relayer has to submit in response to the event.
#[derive(Clone)]
pub struct OperationalData {
    /// Represents the height for the proofs in all the messages. Note that this is the height
    /// at which the proofs are queried. For example, for Tendermint chains, a client consensus
    /// state at `proofs_height + 1` must exist on-chain in order to verify the proofs.
    pub proofs_height: Height,
    /// The batch of messages associated with this piece of operational data.
    pub batch: Vec<TransitMessage>,
    /// Represents the target of the packet messages, either the source or the destination
    /// chain.
    pub target: OperationalDataTarget,
    /// A unique ID for tracking this batch of events starting from when they were received
    /// until the transactions corresponding to those events is submitted.
    pub tracking_id: TrackingId,
    /// Stores `Some(ConnectionDelay)` if the delay is non-zero and `None` otherwise
    connection_delay: Option<ConnectionDelay>,
}

impl OperationalData {
    pub fn new(
        proofs_height: Height,
        target: OperationalDataTarget,
        tracking_id: TrackingId,
        connection_delay: Duration,
    ) -> Self {
        let connection_delay = if !connection_delay.is_zero() {
            Some(ConnectionDelay::new(connection_delay))
        } else {
            None
        };

        OperationalData {
            proofs_height,
            batch: vec![],
            target,
            connection_delay,
            tracking_id,
        }
    }

    pub fn push(&mut self, msg: TransitMessage) {
        self.batch.push(msg)
    }

    /// Returns displayable information on the operation's data.
    pub fn info(&self) -> OperationalInfo {
        OperationalInfo {
            tracking_id: self.tracking_id,
            target: self.target,
            proofs_height: self.proofs_height,
            batch_len: self.batch.len(),
        }
    }

    /// Transforms `self` into the list of events accompanied with the tracking ID.
    pub fn into_events(self) -> TrackedEvents {
        let events = self
            .batch
            .into_iter()
            .map(|gm| gm.event_with_height)
            .collect();

        TrackedEvents {
            events,
            tracking_id: self.tracking_id,
        }
    }

    /// Returns all the messages in this operational
    /// data, plus prepending the client update message
    /// if necessary.
    pub fn assemble_msgs<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        relay_path: &RelayPath<ChainA, ChainB>,
    ) -> Result<TrackedMsgs, LinkError> {
        // For zero delay we prepend the client update msgs.
        let client_update_msg = if !self.conn_delay_needed() {
            let update_height = self.proofs_height.increment();

            debug!(
                "prepending {} client update at height {}",
                self.target, update_height
            );

            // Fetch the client update message. Vector may be empty if the client already has the header
            // for the requested height.
            let mut client_update_opt = match self.target {
                OperationalDataTarget::Source => {
                    relay_path.build_update_client_on_src(update_height)?
                }
                OperationalDataTarget::Destination => {
                    relay_path.build_update_client_on_dst(update_height)?
                }
            };

            client_update_opt.pop()
        } else {
            let (client_state, _) = match self.target {
                OperationalDataTarget::Source => relay_path
                    .src_chain()
                    .query_client_state(
                        QueryClientStateRequest {
                            client_id: relay_path.src_client_id().clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(|e| LinkError::query(relay_path.src_chain().id(), e))?,

                OperationalDataTarget::Destination => relay_path
                    .dst_chain()
                    .query_client_state(
                        QueryClientStateRequest {
                            client_id: relay_path.dst_client_id().clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(|e| LinkError::query(relay_path.dst_chain().id(), e))?,
            };

            if client_state.is_frozen() {
                return Ok(TrackedMsgs::new(vec![], self.tracking_id));
            } else {
                None
            }
        };

        let msgs = client_update_msg
            .into_iter()
            .chain(self.batch.iter().map(|gm| gm.msg.clone()))
            .collect();

        let tm = TrackedMsgs::new(msgs, self.tracking_id);

        info!("assembled batch of {} message(s)", tm.messages().len());

        Ok(tm)
    }

    /// Returns true iff the batch contains a packet event
    fn has_packet_msgs(&self) -> bool {
        self.batch
            .iter()
            .any(|msg| msg.event_with_height.event.packet().is_some())
    }

    /// Returns the `connection_delay` iff the connection delay for this relaying path is non-zero
    /// and the `batch` contains packet messages.
    fn get_delay_if_needed(&self) -> Option<&ConnectionDelay> {
        self.connection_delay
            .as_ref()
            .filter(|_| self.has_packet_msgs())
    }

    /// Returns `true` iff the connection delay for this relaying path is non-zero and `op_data`
    /// contains packet messages.
    pub fn conn_delay_needed(&self) -> bool {
        self.get_delay_if_needed().is_some()
    }

    /// Sets the scheduled time that is used for connection-delay calculations
    pub fn set_scheduled_time(&mut self, scheduled_time: Instant) {
        if let Some(delay) = self.connection_delay.as_mut() {
            delay.scheduled_time = scheduled_time;
        }
    }

    /// Sets the update height that is used for connection-delay calculations
    pub fn set_update_height(&mut self, update_height: Height) {
        if let Some(delay) = self.connection_delay.as_mut() {
            delay.update_height = Some(update_height);
        }
    }

    /// Returns `Ok(remaining-delay)` on success or `LinkError` if the input closure fails.
    fn conn_time_delay_remaining<ChainTime>(
        &self,
        chain_time: &ChainTime,
    ) -> Result<Duration, LinkError>
    where
        ChainTime: Fn() -> Result<Instant, LinkError>,
    {
        if let Some(delay) = self.get_delay_if_needed() {
            Ok(delay.conn_time_delay_remaining(chain_time()?))
        } else {
            Ok(Duration::ZERO)
        }
    }

    /// Returns `Ok(remaining-delay)` on success or `LinkError` if an input closure fails.
    fn conn_block_delay_remaining<MaxBlockTime, LatestHeight>(
        &self,
        max_expected_time_per_block: &MaxBlockTime,
        latest_height: &LatestHeight,
    ) -> Result<u64, LinkError>
    where
        MaxBlockTime: Fn() -> Result<Duration, LinkError>,
        LatestHeight: Fn() -> Result<Height, LinkError>,
    {
        if let Some(delay) = self.get_delay_if_needed() {
            let block_delay = delay.conn_block_delay(max_expected_time_per_block()?);
            Ok(delay.conn_block_delay_remaining(block_delay, latest_height()?))
        } else {
            Ok(0)
        }
    }

    pub fn has_conn_delay_elapsed<ChainTime, MaxBlockTime, LatestHeight>(
        &self,
        chain_time: &ChainTime,
        max_expected_time_per_block: &MaxBlockTime,
        latest_height: &LatestHeight,
    ) -> Result<bool, LinkError>
    where
        ChainTime: Fn() -> Result<Instant, LinkError>,
        MaxBlockTime: Fn() -> Result<Duration, LinkError>,
        LatestHeight: Fn() -> Result<Height, LinkError>,
    {
        Ok(self.conn_time_delay_remaining(chain_time)?.is_zero()
            && self.conn_block_delay_remaining(max_expected_time_per_block, latest_height)? == 0)
    }

    pub fn conn_delay_remaining<ChainTime, MaxBlockTime, LatestHeight>(
        &self,
        chain_time: &ChainTime,
        max_expected_time_per_block: &MaxBlockTime,
        latest_height: &LatestHeight,
    ) -> Result<(Duration, u64), LinkError>
    where
        ChainTime: Fn() -> Result<Instant, LinkError>,
        MaxBlockTime: Fn() -> Result<Duration, LinkError>,
        LatestHeight: Fn() -> Result<Height, LinkError>,
    {
        Ok((
            self.conn_time_delay_remaining(chain_time)?,
            self.conn_block_delay_remaining(max_expected_time_per_block, latest_height)?,
        ))
    }
}

/// A struct that holds everything that is required to calculate and deal with the connection-delay
/// feature.
#[derive(Clone)]
struct ConnectionDelay {
    delay: Duration,
    scheduled_time: Instant,
    update_height: Option<Height>,
}

impl ConnectionDelay {
    fn new(delay: Duration) -> Self {
        Self {
            delay,
            scheduled_time: Instant::now(),
            update_height: None,
        }
    }

    /// Returns `remaining-delay` if connection-delay hasn't elapsed and `Duration::ZERO` otherwise.
    fn conn_time_delay_remaining(&self, chain_time: Instant) -> Duration {
        // since chain time instant is relative to relayer's current time, it is possible that
        // `scheduled_time` is later (by nano secs) than `chain_time`, hence the call to
        // `saturating_duration_since()`.
        let elapsed = chain_time.saturating_duration_since(self.scheduled_time);
        if elapsed >= self.delay {
            Duration::ZERO
        } else {
            self.delay - elapsed
        }
    }

    /// Returns `remaining-delay` if connection-delay hasn't elapsed and `0` otherwise.
    fn conn_block_delay_remaining(&self, block_delay: u64, latest_height: Height) -> u64 {
        let acceptable_height = self
            .update_height
            .expect("processed height not set")
            .add(block_delay);

        if latest_height >= acceptable_height {
            0
        } else {
            debug_assert!(acceptable_height.revision_number() == latest_height.revision_number());
            acceptable_height.revision_height() - latest_height.revision_height()
        }
    }

    /// Calculates and returns the block-delay based on the `max_expected_time_per_block`
    fn conn_block_delay(&self, max_expected_time_per_block: Duration) -> u64 {
        calculate_block_delay(self.delay, max_expected_time_per_block)
    }
}

fn calculate_block_delay(
    delay_period_time: Duration,
    max_expected_time_per_block: Duration,
) -> u64 {
    if max_expected_time_per_block.is_zero() {
        return 0;
    }

    (delay_period_time.as_secs_f64() / max_expected_time_per_block.as_secs_f64()).ceil() as u64
}

/// A lightweight informational data structure that can be extracted
/// out of [`OperationalData`] for e.g. logging purposes.
pub struct OperationalInfo {
    tracking_id: TrackingId,
    target: OperationalDataTarget,
    proofs_height: Height,
    batch_len: usize,
}

impl OperationalInfo {
    pub fn target(&self) -> OperationalDataTarget {
        self.target
    }

    /// Returns the length of the assembled batch of in-transit messages.
    pub fn batch_len(&self) -> usize {
        self.batch_len
    }
}

impl Display for OperationalInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "{} ->{} @{}; len={}",
            self.tracking_id, self.target, self.proofs_height, self.batch_len,
        )
    }
}
