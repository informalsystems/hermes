#![allow(clippy::borrowed_box)]

use core::marker::PhantomData;
use prost_types::Any;
use std::time::Duration;
use tracing::{debug, error, info, warn};

use ibc::events::IbcEvent;
use ibc::ics04_channel::channel::{self, Order, State};
use ibc::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
use ibc::ics04_channel::msgs::chan_close_init::MsgChannelCloseInit;
use ibc::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::tagged::{DualTagged, Tagged};
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::QueryConnectionChannelsRequest;

use crate::chain::counterparty::{channel_connection_client, channel_state_on_destination};
use crate::chain::handle::ChainHandle;
use crate::connection::Connection;
use crate::foreign_client::ForeignClient;
use crate::object::Channel as WorkerChannelObject;
use crate::supervisor::error::Error as SupervisorError;
use crate::util::retry::retry_with_index;
use crate::util::retry::RetryResult;

pub mod error;
pub use error::ChannelError;

mod retry_strategy {
    use std::time::Duration;

    use retry::delay::Fibonacci;

    use crate::util::retry::clamp_total;

    // Default parameters for the retrying mechanism
    const MAX_DELAY: Duration = Duration::from_secs(60); // 1 minute
    const MAX_TOTAL_DELAY: Duration = Duration::from_secs(10 * 60); // 10 minutes
    const INITIAL_DELAY: Duration = Duration::from_secs(1); // 1 second

    pub fn default() -> impl Iterator<Item = Duration> {
        clamp_total(Fibonacci::from(INITIAL_DELAY), MAX_DELAY, MAX_TOTAL_DELAY)
    }
}

pub fn from_retry_error(e: retry::Error<ChannelError>, description: String) -> ChannelError {
    match e {
        retry::Error::Operation {
            error,
            total_delay,
            tries,
        } => {
            let detail = error::ChannelErrorDetail::MaxRetry(error::MaxRetrySubdetail {
                description,
                tries,
                total_delay,
                source: Box::new(error.0),
            });
            ChannelError(detail, error.1)
        }
        retry::Error::Internal(reason) => ChannelError::retry_internal(reason),
    }
}

#[derive(Debug, Clone)]
pub struct ChannelEnd<ChainA, ChainB>(pub DualTagged<ChainA, ChainB, channel::ChannelEnd>);

#[derive(Debug, Clone)]
pub struct IdentifiedChannelEnd<ChainA, ChainB>(
    pub DualTagged<ChainA, ChainB, channel::IdentifiedChannelEnd>,
);

#[derive(Debug, Clone)]
pub struct Counterparty<Chain>(pub Tagged<Chain, channel::Counterparty>);

impl<ChainA, ChainB> ChannelEnd<ChainA, ChainB> {
    pub fn new(
        state: Tagged<ChainA, State>,
        ordering: Order,
        remote: Counterparty<ChainB>,
        connection_hops: Vec<Tagged<ChainA, ConnectionId>>,
        version: String,
    ) -> Self {
        Self(DualTagged::new(channel::ChannelEnd::new(
            state.untag(),
            ordering,
            remote.0.untag(),
            connection_hops.into_iter().map(|c| c.untag()).collect(),
            version,
        )))
    }

    pub fn tag(channel: channel::ChannelEnd) -> Self {
        Self(DualTagged::new(channel))
    }

    pub fn value(&self) -> &channel::ChannelEnd {
        self.0.value()
    }

    pub fn state(&self) -> Tagged<ChainA, State> {
        self.0.map(|c| c.state.clone())
    }

    pub fn ordering(&self) -> Order {
        self.value().ordering.clone()
    }

    pub fn counterparty(&self) -> Counterparty<ChainB> {
        Counterparty(self.0.map_flipped(|c| c.counterparty().clone()))
    }

    pub fn version(&self) -> String {
        self.0.value().version()
    }

    pub fn connection_hops(&self) -> Vec<Tagged<ChainA, ConnectionId>> {
        self.0
            .value()
            .connection_hops()
            .iter()
            .map(|c| Tagged::new(c.clone()))
            .collect()
    }
}

impl<ChainA, ChainB> IdentifiedChannelEnd<ChainA, ChainB> {
    pub fn new(
        port_id: Tagged<ChainA, PortId>,
        channel_id: Tagged<ChainA, ChannelId>,
        channel_end: ChannelEnd<ChainA, ChainB>,
    ) -> Self {
        Self(DualTagged::new(channel::IdentifiedChannelEnd::new(
            port_id.untag(),
            channel_id.untag(),
            channel_end.0.untag(),
        )))
    }

    pub fn tag(channel: channel::IdentifiedChannelEnd) -> Self {
        Self(DualTagged::new(channel))
    }

    pub fn value(&self) -> &channel::IdentifiedChannelEnd {
        self.0.value()
    }

    pub fn channel_id(&self) -> Tagged<ChainA, ChannelId> {
        self.0.map(|c| c.channel_id.clone())
    }

    pub fn port_id(&self) -> Tagged<ChainA, PortId> {
        self.0.map(|c| c.port_id.clone())
    }

    pub fn channel_end(&self) -> ChannelEnd<ChainA, ChainB> {
        ChannelEnd(self.0.dual_map(|c| c.channel_end.clone()))
    }

    pub fn counterparty(&self) -> Counterparty<ChainB> {
        self.channel_end().counterparty()
    }
}

impl<Chain> Counterparty<Chain> {
    pub fn new(
        port_id: Tagged<Chain, PortId>,
        channel_id: Option<Tagged<Chain, ChannelId>>,
    ) -> Self {
        Self(Tagged::new(channel::Counterparty::new(
            port_id.untag(),
            channel_id.map(Tagged::untag),
        )))
    }

    pub fn tag(counterparty: channel::Counterparty) -> Self {
        Self(Tagged::new(counterparty))
    }

    pub fn value(&self) -> &channel::Counterparty {
        self.0.value()
    }

    pub fn port_id(&self) -> Tagged<Chain, PortId> {
        self.0.map(|c| c.port_id().clone())
    }

    pub fn channel_id(&self) -> Option<Tagged<Chain, ChannelId>> {
        self.0.map(|c| c.channel_id().clone()).transpose()
    }
}

#[derive(Clone, Debug)]
pub struct ChannelSide<Chain, Counterparty>
where
    Chain: ChainHandle<Counterparty>,
{
    pub chain: Chain,
    client_id: Tagged<Chain, ClientId>,
    connection_id: Tagged<Chain, ConnectionId>,
    port_id: Tagged<Chain, PortId>,
    channel_id: Option<Tagged<Chain, ChannelId>>,
    phantom: PhantomData<Counterparty>,
}

impl<Chain, CounterpartyChain> ChannelSide<Chain, CounterpartyChain>
where
    Chain: ChainHandle<CounterpartyChain>,
{
    pub fn new(
        chain: Chain,
        client_id: Tagged<Chain, ClientId>,
        connection_id: Tagged<Chain, ConnectionId>,
        port_id: Tagged<Chain, PortId>,
        channel_id: Option<Tagged<Chain, ChannelId>>,
    ) -> ChannelSide<Chain, CounterpartyChain> {
        Self {
            chain,
            client_id,
            connection_id,
            port_id,
            channel_id,
            phantom: PhantomData,
        }
    }

    pub fn chain_id(&self) -> Tagged<Chain, ChainId> {
        self.chain.id()
    }

    pub fn client_id(&self) -> Tagged<Chain, ClientId> {
        self.client_id.clone()
    }

    pub fn connection_id(&self) -> Tagged<Chain, ConnectionId> {
        self.connection_id.clone()
    }

    pub fn port_id(&self) -> Tagged<Chain, PortId> {
        self.port_id.clone()
    }

    pub fn channel_id(&self) -> Option<Tagged<Chain, ChannelId>> {
        self.channel_id.clone()
    }
}

#[derive(Clone, Debug)]
pub struct Channel<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    // ordering must be the same on both sides
    pub ordering: Order,

    pub a_side: ChannelSide<ChainA, ChainB>,
    pub b_side: ChannelSide<ChainB, ChainA>,
    pub connection_delay: Duration,
    pub version: Option<String>,
}

impl<ChainA, ChainB> Channel<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    /// Creates a new channel on top of the existing connection. If the channel is not already
    /// set-up on both sides of the connection, this functions also fulfils the channel handshake.
    pub fn create(
        connection: Connection<ChainA, ChainB>,
        ordering: Order,
        a_port: Tagged<ChainA, PortId>,
        b_port: Tagged<ChainB, PortId>,
        version: Option<String>,
    ) -> Result<Self, ChannelError> {
        let b_side_chain = connection.dst_chain();
        let version = version.unwrap_or(
            b_side_chain
                .module_version(b_port)
                .map_err(|e| ChannelError::query(b_side_chain.id().value().clone(), e))?,
        );

        let src_connection_id = connection.src_connection_id().ok_or_else(|| {
            ChannelError::missing_local_connection(connection.src_chain().id().value().clone())
        })?;
        let dst_connection_id = connection.dst_connection_id().ok_or_else(|| {
            ChannelError::missing_local_connection(connection.dst_chain().id().value().clone())
        })?;

        let mut channel = Self {
            ordering,
            a_side: ChannelSide::new(
                connection.src_chain().clone(),
                connection.src_client_id().clone(),
                src_connection_id.clone(),
                a_port,
                Default::default(),
            ),
            b_side: ChannelSide::new(
                connection.dst_chain().clone(),
                connection.dst_client_id().clone(),
                dst_connection_id.clone(),
                b_port,
                Default::default(),
            ),
            connection_delay: connection.delay_period,
            version: Some(version),
        };

        channel.handshake()?;

        Ok(channel)
    }

    pub fn restore_from_event(
        chain: ChainA,
        counterparty_chain: ChainB,
        channel_open_event: DualTagged<ChainA, ChainB, IbcEvent>,
    ) -> Result<Channel<ChainA, ChainB>, ChannelError> {
        let channel_event_attributes = channel_open_event
            .dual_map(|e| e.channel_attributes().clone())
            .transpose()
            .ok_or_else(|| ChannelError::invalid_event(channel_open_event.untag()))?;

        let port_id = channel_event_attributes.map(|a| a.port_id.clone());
        let channel_id = channel_event_attributes
            .map(|a| a.channel_id.clone())
            .transpose();

        let connection_id = channel_event_attributes.map(|a| a.connection_id.clone());

        let connection = chain
            .query_connection(connection_id, Height::tagged_zero())
            .map_err(ChannelError::relayer)?;

        let connection_counterparty = connection.counterparty();

        let counterparty_connection_id = connection_counterparty
            .connection_id()
            .ok_or_else(ChannelError::missing_counterparty_connection)?;

        let counterparty_port_id = channel_event_attributes.map_flipped(|a| a.counterparty_port_id);

        let counterparty_channel_id = channel_event_attributes
            .map_flipped(|a| a.counterparty_channel_id)
            .transpose();

        let version = counterparty_chain
            .module_version(counterparty_port_id)
            .map_err(|e| ChannelError::query(counterparty_chain.id().untag(), e))?;

        Ok(Channel {
            // The event does not include the channel ordering.
            // The message handlers `build_chan_open..` determine the order included in the handshake
            // message from channel query.
            ordering: Default::default(),
            a_side: ChannelSide::new(
                chain,
                connection.client_id(),
                connection_id,
                port_id,
                channel_id,
            ),
            b_side: ChannelSide::new(
                counterparty_chain,
                connection_counterparty.client_id(),
                counterparty_connection_id.clone(),
                counterparty_port_id,
                counterparty_channel_id,
            ),
            connection_delay: connection.delay_period(),
            // The event does not include the version.
            // The message handlers `build_chan_open..` determine the version from channel query.
            version: Some(version),
        })
    }

    /// Recreates a 'Channel' object from the worker's object built from chain state scanning.
    /// The channel must exist on chain and its connection must be initialized on both chains.
    pub fn restore_from_state(
        chain: ChainA,
        counterparty_chain: ChainB,
        channel: WorkerChannelObject<ChainB, ChainA>,
        height: Tagged<ChainA, Height>,
    ) -> Result<(Channel<ChainA, ChainB>, State), ChannelError> {
        let src_port_id = channel.src_port_id();
        let src_channel_id = channel.src_channel_id();

        let a_channel = chain
            .query_channel(src_port_id, src_channel_id, height)
            .map_err(ChannelError::relayer)?;

        let a_connection_id = a_channel
            .connection_hops()
            .first()
            .map(Clone::clone)
            .ok_or_else(|| {
                ChannelError::supervisor(SupervisorError::missing_connection_hops(
                    src_channel_id.untag(),
                    chain.id().untag(),
                ))
            })?;

        let a_connection = chain
            .query_connection(a_connection_id, Height::tagged_zero())
            .map_err(ChannelError::relayer)?;

        let b_connection = a_connection.counterparty();

        let b_connection_id = b_connection.connection_id().ok_or_else(|| {
            ChannelError::supervisor(SupervisorError::channel_connection_uninitialized(
                src_channel_id.untag(),
                chain.id().untag(),
                b_connection.0.untag(),
            ))
        })?;

        let b_channel = a_channel.counterparty();

        let mut handshake_channel = Channel {
            ordering: a_channel.ordering(),
            a_side: ChannelSide::new(
                chain.clone(),
                a_connection.client_id(),
                a_connection_id.clone(),
                src_port_id,
                Some(src_channel_id),
            ),
            b_side: ChannelSide::new(
                counterparty_chain.clone(),
                b_connection.client_id(),
                b_connection_id.clone(),
                b_channel.port_id(),
                b_channel.channel_id(),
            ),
            connection_delay: a_connection.delay_period(),
            version: Some(a_channel.value().version.clone()),
        };

        if a_channel.value().state_matches(&State::Init) && b_channel.value().channel_id.is_none() {
            let req = QueryConnectionChannelsRequest {
                connection: b_connection_id.to_string(),
                pagination: ibc_proto::cosmos::base::query::pagination::all(),
            };

            let b_channels = counterparty_chain
                .query_connection_channels(req)
                .map_err(ChannelError::relayer)?;

            for b_channel in b_channels {
                let a_channel = b_channel.counterparty();

                let b_channel_id = b_channel.channel_id();

                let m_a_channel_id = a_channel.channel_id();

                if let Some(a_channel_id) = m_a_channel_id {
                    if a_channel_id == src_channel_id {
                        handshake_channel.b_side.channel_id = Some(b_channel_id);
                        break;
                    }
                }
            }
        }

        Ok((handshake_channel, a_channel.state().untag()))
    }

    pub fn src_chain(&self) -> &ChainA {
        &self.a_side.chain
    }

    pub fn dst_chain(&self) -> &ChainB {
        &self.b_side.chain
    }

    pub fn src_client_id(&self) -> Tagged<ChainA, ClientId> {
        self.a_side.client_id.clone()
    }

    pub fn dst_client_id(&self) -> Tagged<ChainB, ClientId> {
        self.b_side.client_id.clone()
    }

    pub fn src_connection_id(&self) -> Tagged<ChainA, ConnectionId> {
        self.a_side.connection_id.clone()
    }

    pub fn dst_connection_id(&self) -> Tagged<ChainB, ConnectionId> {
        self.b_side.connection_id.clone()
    }

    pub fn src_port_id(&self) -> Tagged<ChainA, PortId> {
        self.a_side.port_id.clone()
    }

    pub fn dst_port_id(&self) -> Tagged<ChainB, PortId> {
        self.b_side.port_id.clone()
    }

    pub fn src_channel_id(&self) -> Option<Tagged<ChainA, ChannelId>> {
        self.a_side.channel_id()
    }

    pub fn dst_channel_id(&self) -> Option<Tagged<ChainB, ChannelId>> {
        self.b_side.channel_id()
    }

    pub fn flipped(&self) -> Channel<ChainB, ChainA> {
        Channel {
            ordering: self.ordering,
            a_side: self.b_side.clone(),
            b_side: self.a_side.clone(),
            connection_delay: self.connection_delay,
            version: self.version.clone(),
        }
    }

    fn do_chan_open_init_and_send(&mut self) -> Result<(), ChannelError> {
        let event = self.flipped().build_chan_open_init_and_send()?;

        info!("done {} => {:#?}\n", self.src_chain().id(), event);

        let channel_id = event.map(|e| extract_channel_id(e)).transpose()?;
        self.a_side.channel_id = Some(channel_id);
        info!("successfully opened init channel");

        Ok(())
    }

    // Check that the channel was created on a_chain
    fn do_chan_open_init_and_send_with_retry(&mut self) -> Result<(), ChannelError> {
        retry_with_index(retry_strategy::default(), |_| {
            self.do_chan_open_init_and_send()
        })
        .map_err(|err| {
            error!("failed to open channel after {} retries", err);

            from_retry_error(
                err,
                format!("Failed to finish channel open init for {:?}", self),
            )
        })?;

        Ok(())
    }

    fn do_chan_open_try_and_send(&mut self) -> Result<(), ChannelError> {
        let event = self.build_chan_open_try_and_send().map_err(|e| {
            error!("Failed ChanTry {:?}: {:?}", self.b_side, e);
            e
        })?;

        let channel_id = event.map(|e| extract_channel_id(e)).transpose()?;

        self.b_side.channel_id = Some(channel_id.clone());

        println!("done {} => {:#?}\n", self.dst_chain().id(), event);
        Ok(())
    }

    fn do_chan_open_try_and_send_with_retry(&mut self) -> Result<(), ChannelError> {
        retry_with_index(retry_strategy::default(), |_| {
            self.do_chan_open_try_and_send()
        })
        .map_err(|err| {
            error!("failed to open channel after {} retries", err);

            from_retry_error(
                err,
                format!("Failed to finish channel open try for {:?}", self),
            )
        })?;

        Ok(())
    }

    /// Sends the last two steps, consisting of `Ack` and `Confirm`
    /// messages, for finalizing the channel open handshake.
    ///
    /// Assumes that the channel open handshake was previously
    /// started (with `Init` & `Try` steps).
    ///
    /// Returns `Ok` when both channel ends are in state `Open`.
    /// Also returns `Ok` if the channel is undergoing a closing handshake.
    ///
    /// An `Err` can signal two cases:
    ///     - the common-case flow for the handshake protocol was interrupted,
    ///         e.g., by a competing relayer.
    ///     - Rpc problems (a query or submitting a tx failed).
    /// In both `Err` cases, there should be retry calling this method.
    fn do_chan_open_finalize(&self) -> Result<(), ChannelError> {
        fn query_channel_states<ChainA, ChainB>(
            channel: &Channel<ChainA, ChainB>,
        ) -> Result<(Tagged<ChainA, State>, Tagged<ChainB, State>), ChannelError>
        where
            ChainA: ChainHandle<ChainB>,
            ChainB: ChainHandle<ChainA>,
        {
            let src_channel_id = channel
                .src_channel_id()
                .ok_or_else(ChannelError::missing_local_channel_id)?;

            let dst_channel_id = channel
                .dst_channel_id()
                .ok_or_else(ChannelError::missing_counterparty_connection)?;

            debug!(
                "do_chan_open_finalize for src_channel_id: {}, dst_channel_id: {}",
                src_channel_id, dst_channel_id
            );

            // Continue loop if query error
            let a_channel = channel
                .src_chain()
                .query_channel(channel.src_port_id(), src_channel_id, Height::tagged_zero())
                .map_err(|e| {
                    ChannelError::handshake_finalize(
                        channel.src_port_id().value().clone(),
                        src_channel_id.value().clone(),
                        channel.src_chain().id().untag(),
                        e,
                    )
                })?;

            let b_channel = channel
                .dst_chain()
                .query_channel(channel.dst_port_id(), dst_channel_id, Height::tagged_zero())
                .map_err(|e| {
                    ChannelError::handshake_finalize(
                        channel.dst_port_id().value().clone(),
                        dst_channel_id.value().clone(),
                        channel.dst_chain().id().untag(),
                        e,
                    )
                })?;

            let a_state = a_channel.state();
            let b_state = b_channel.state();

            Ok((a_state, b_state))
        }

        fn expect_channel_states<ChainA, ChainB>(
            ctx: &Channel<ChainA, ChainB>,
            a1: State,
            b1: State,
        ) -> Result<(), ChannelError>
        where
            ChainA: ChainHandle<ChainB>,
            ChainB: ChainHandle<ChainA>,
        {
            let (a2, b2) = query_channel_states(ctx)?;

            if (a1, b1) == (a2.untag(), b2.untag()) {
                Ok(())
            } else {
                warn!(
                    "expected channels to progress to states {}, {}), instead got ({}, {})",
                    a1, b1, a2, b2
                );

                debug!("returning PartialOpenHandshake to retry");

                // One more step (confirm) left.
                // Returning error signals that the caller should retry.
                Err(ChannelError::partial_open_handshake(a1, b1))
            }
        }

        let (a_state, b_state) = query_channel_states(self)?;
        debug!(
            "do_chan_open_finalize with channel states: {}, {}",
            a_state, b_state
        );

        match (a_state.untag(), b_state.untag()) {
            // Handle sending the Ack message to the source chain,
            // then the Confirm message to the destination.
            (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                self.flipped().build_chan_open_ack_and_send()?;

                expect_channel_states(self, State::Open, State::TryOpen)?;

                self.build_chan_open_confirm_and_send()?;

                expect_channel_states(self, State::Open, State::Open)?;

                Ok(())
            }

            // Handle sending the Ack message to the destination chain,
            // then the Confirm to the source chain.
            (State::TryOpen, State::Init) => {
                self.flipped().build_chan_open_ack_and_send()?;

                expect_channel_states(self, State::TryOpen, State::Open)?;

                self.flipped().build_chan_open_confirm_and_send()?;

                expect_channel_states(self, State::Open, State::Open)?;

                Ok(())
            }

            // Handle sending the Confirm message to the destination chain.
            (State::Open, State::TryOpen) => {
                self.build_chan_open_confirm_and_send()?;

                expect_channel_states(self, State::Open, State::Open)?;

                Ok(())
            }

            // Send Confirm to the source chain.
            (State::TryOpen, State::Open) => {
                self.flipped().build_chan_open_confirm_and_send()?;

                expect_channel_states(self, State::Open, State::Open)?;

                Ok(())
            }

            (State::Open, State::Open) => {
                info!("channel handshake already finished for {:#?}\n", self);
                Ok(())
            }

            // In all other conditions, return Ok, since the channel open handshake does not apply.
            _ => Ok(()),
        }
    }

    /// Takes a partially open channel and finalizes the open handshake protocol.
    ///
    /// Pre-condition: the channel identifiers are established on both ends
    ///   (i.e., `OpenInit` and `OpenTry` have executed previously for this channel).
    ///
    /// Post-condition: the channel state is `Open` on both ends if successful.
    fn do_chan_open_finalize_with_retry(&self) -> Result<(), ChannelError> {
        retry_with_index(retry_strategy::default(), |_| self.do_chan_open_finalize()).map_err(
            |err| {
                error!("failed to open channel after {} retries", err);
                from_retry_error(
                    err,
                    format!("Failed to finish channel handshake for {:?}", self),
                )
            },
        )?;

        Ok(())
    }

    /// Executes the channel handshake protocol (ICS004)
    fn handshake(&mut self) -> Result<(), ChannelError> {
        self.do_chan_open_init_and_send_with_retry()?;
        self.do_chan_open_try_and_send_with_retry()?;
        self.do_chan_open_finalize_with_retry()
    }

    pub fn counterparty_state(&self) -> Result<Tagged<ChainB, State>, ChannelError> {
        // Source channel ID must be specified
        let channel_id = self
            .src_channel_id()
            .ok_or_else(ChannelError::missing_local_channel_id)?;

        let channel_deps =
            channel_connection_client(self.src_chain(), self.src_port_id(), channel_id)
                .map_err(|e| ChannelError::query_channel(channel_id.untag(), e))?;

        channel_state_on_destination(
            channel_deps.channel,
            channel_deps.connection,
            self.dst_chain(),
        )
        .map_err(|e| ChannelError::query_channel(channel_id.value().clone(), e))
    }

    pub fn handshake_step(
        &mut self,
        state: State,
    ) -> Result<Vec<Tagged<ChainB, IbcEvent>>, ChannelError> {
        match (state, self.counterparty_state()?.value()) {
            (State::Init, State::Uninitialized) => Ok(vec![self.build_chan_open_try_and_send()?]),
            (State::Init, State::Init) => Ok(vec![self.build_chan_open_try_and_send()?]),
            (State::TryOpen, State::Init) => Ok(vec![self.build_chan_open_ack_and_send()?]),
            (State::TryOpen, State::TryOpen) => Ok(vec![self.build_chan_open_ack_and_send()?]),
            (State::Open, State::TryOpen) => Ok(vec![self.build_chan_open_confirm_and_send()?]),
            _ => Ok(vec![]),
        }
    }

    pub fn step_state(&mut self, state: State, index: u64) -> RetryResult<(), u64> {
        let done = '🥳';

        match self.handshake_step(state) {
            Err(e) => {
                error!("Failed Chan{:?} with error: {}", state, e);
                RetryResult::Retry(index)
            }
            Ok(ev) => {
                debug!("{} => {:#?}\n", done, ev);
                RetryResult::Ok(())
            }
        }
    }

    pub fn step_event(&mut self, event: IbcEvent, index: u64) -> RetryResult<(), u64> {
        let state = match event {
            IbcEvent::OpenInitChannel(_) => State::Init,
            IbcEvent::OpenTryChannel(_) => State::TryOpen,
            IbcEvent::OpenAckChannel(_) => State::Open,
            IbcEvent::OpenConfirmChannel(_) => State::Open,
            _ => State::Uninitialized,
        };

        self.step_state(state, index)
    }

    pub fn build_update_client_on_dst(
        &self,
        height: Tagged<ChainA, Height>,
    ) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        let client = ForeignClient::restore(
            self.dst_client_id().clone(),
            self.dst_chain().clone(),
            self.src_chain().clone(),
        );

        client.build_update_client(height).map_err(|e| {
            ChannelError::client_operation(
                self.dst_client_id().value().clone(),
                self.dst_chain().id().untag(),
                e,
            )
        })
    }

    /// Returns the channel version if already set, otherwise it queries the destination chain
    /// for the destination port's version.
    /// Note: This query is currently not available and it is hardcoded in the `module_version()`
    /// to be `ics20-1` for `transfer` port.
    pub fn dst_version(&self) -> Result<String, ChannelError> {
        Ok(self.version.clone().unwrap_or(
            self.dst_chain()
                .module_version(self.dst_port_id())
                .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?,
        ))
    }

    /// Returns the channel version if already set, otherwise it queries the source chain
    /// for the source port's version.
    pub fn src_version(&self) -> Result<String, ChannelError> {
        Ok(self.version.clone().unwrap_or(
            self.src_chain()
                .module_version(self.src_port_id())
                .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?,
        ))
    }

    pub fn build_chan_open_init(&self) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        let counterparty = Counterparty::new(self.src_port_id(), None);

        let channel = ChannelEnd::new(
            Tagged::new(State::Init),
            self.ordering,
            counterparty,
            vec![self.dst_connection_id()],
            self.dst_version()?,
        );

        // Build the domain type message
        let new_msg = MsgChannelOpenInit::tagged_new(self.dst_port_id(), channel.0, signer);

        Ok(vec![new_msg.map_into(Msg::to_any)])
    }

    pub fn build_chan_open_init_and_send(&self) -> Result<Tagged<ChainB, IbcEvent>, ChannelError> {
        let dst_msgs = self.build_chan_open_init()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::submit(self.dst_chain().id().untag(), e))?;

        for event in events {
            match event.value() {
                IbcEvent::OpenInitChannel(_) => {
                    return Ok(event);
                }
                IbcEvent::ChainError(e) => {
                    return Err(ChannelError::tx_response(e.clone()));
                }
                _ => {}
            }
        }

        Err(ChannelError::missing_event(
            "no chan init event was in the response".to_string(),
        ))
    }

    /// Retrieves the channel from destination and compares against the expected channel
    /// built from the message type (`msg_type`) and options (`opts`).
    /// If the expected and the destination channels are compatible, it returns the expected channel
    /// Source and destination channel IDs must be specified.
    fn validated_expected_channel(
        &self,
        msg_type: ChannelMsgType,
    ) -> Result<ChannelEnd<ChainB, ChainA>, ChannelError> {
        // Destination channel ID must be specified
        let dst_channel_id = self
            .dst_channel_id()
            .ok_or_else(ChannelError::missing_counterparty_channel_id)?;

        // If there is a channel present on the destination chain, it should look like this:
        let counterparty = Counterparty::new(self.src_port_id(), self.src_channel_id());

        // The highest expected state, depends on the message type:
        let highest_state = match msg_type {
            ChannelMsgType::OpenAck => State::TryOpen,
            ChannelMsgType::OpenConfirm => State::TryOpen,
            ChannelMsgType::CloseConfirm => State::Open,
            _ => State::Uninitialized,
        };

        let dst_expected_channel = ChannelEnd::new(
            Tagged::new(highest_state),
            self.ordering,
            counterparty,
            vec![self.dst_connection_id()],
            self.dst_version()?,
        );

        // Retrieve existing channel
        let dst_channel = self
            .dst_chain()
            .query_channel(self.dst_port_id(), dst_channel_id, Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        // Check if a channel is expected to exist on destination chain
        // A channel must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dst_channel.value().state_matches(&State::Uninitialized) {
            return Err(ChannelError::missing_channel_on_destination());
        }

        check_destination_channel_state(
            dst_channel_id.clone(),
            dst_channel,
            dst_expected_channel.clone(),
        )?;

        Ok(dst_expected_channel)
    }

    pub fn build_chan_open_try(&self) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        // Source channel ID must be specified
        let src_channel_id = self
            .src_channel_id()
            .ok_or_else(ChannelError::missing_local_channel_id)?;

        // Channel must exist on source
        let src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), src_channel_id, Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        let dst_channel = src_channel.counterparty();
        let dst_port_id = dst_channel.port_id();

        if dst_port_id != self.dst_port_id() {
            return Err(ChannelError::mismatch_port(
                self.dst_chain().id().untag(),
                self.dst_port_id().value().clone(),
                self.src_chain().id().untag(),
                dst_port_id.untag(),
                src_channel_id.value().clone(),
            ));
        }

        // Connection must exist on destination
        self.dst_chain()
            .query_connection(self.dst_connection_id(), Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, query_height)
            .map_err(ChannelError::channel_proof)?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.map(|p| p.height()))?;

        let counterparty = Counterparty::new(self.src_port_id(), self.src_channel_id());

        let channel = ChannelEnd::new(
            Tagged::new(State::TryOpen),
            src_channel.ordering(),
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_version()?,
        );

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ChannelError::fetch_signer(self.dst_chain().id().untag(), e))?;

        let dst_channel = src_channel.counterparty();

        let previous_channel_id = if dst_channel.channel_id().is_none() {
            self.b_side.channel_id.clone()
        } else {
            dst_channel.channel_id()
        };

        // Build the domain type message
        let new_msg = MsgChannelOpenTry::new_tagged(
            self.dst_port_id(),
            previous_channel_id,
            channel.0,
            self.src_version()?,
            proofs,
            signer,
        );

        msgs.push(new_msg.map_into(Msg::to_any));
        Ok(msgs)
    }

    pub fn build_chan_open_try_and_send(&self) -> Result<Tagged<ChainB, IbcEvent>, ChannelError> {
        let dst_msgs = self.build_chan_open_try()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::submit(self.dst_chain().id().untag(), e))?;

        for event in events {
            match event.value() {
                IbcEvent::OpenTryChannel(_) => {
                    return Ok(event);
                }
                IbcEvent::ChainError(e) => {
                    return Err(ChannelError::tx_response(e.clone()));
                }
                _ => {}
            }
        }

        Err(ChannelError::missing_event(
            "no chan try event was in the response".to_string(),
        ))
    }

    pub fn build_chan_open_ack(&self) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        // Source and destination channel IDs must be specified
        let src_channel_id = self
            .src_channel_id()
            .ok_or_else(ChannelError::missing_local_channel_id)?;
        let dst_channel_id = self
            .dst_channel_id()
            .ok_or_else(ChannelError::missing_counterparty_channel_id)?;

        // Check that the destination chain will accept the message
        self.validated_expected_channel(ChannelMsgType::OpenAck)?;

        // Channel must exist on source
        self.src_chain()
            .query_channel(self.src_port_id(), src_channel_id, Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        // Connection must exist on destination
        self.dst_chain()
            .query_connection(self.dst_connection_id(), Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, query_height)
            .map_err(ChannelError::channel_proof)?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.map(|p| p.height()))?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ChannelError::fetch_signer(self.dst_chain().id().untag(), e))?;

        // Build the domain type message
        let new_msg = MsgChannelOpenAck::tagged_new(
            self.dst_port_id(),
            dst_channel_id,
            src_channel_id,
            self.src_version()?,
            proofs,
            signer,
        );

        msgs.push(new_msg.map_into(Msg::to_any));
        Ok(msgs)
    }

    pub fn build_chan_open_ack_and_send(&self) -> Result<Tagged<ChainB, IbcEvent>, ChannelError> {
        fn do_build_chan_open_ack_and_send<ChainA, ChainB>(
            channel: &Channel<ChainA, ChainB>,
        ) -> Result<Tagged<ChainB, IbcEvent>, ChannelError>
        where
            ChainA: ChainHandle<ChainB>,
            ChainB: ChainHandle<ChainA>,
        {
            let dst_msgs = channel.build_chan_open_ack()?;

            let events = channel
                .dst_chain()
                .send_msgs(dst_msgs)
                .map_err(|e| ChannelError::submit(channel.dst_chain().id().untag(), e))?;

            // Find the relevant event for channel open ack
            for event in events {
                match event.untag() {
                    IbcEvent::OpenAckChannel(_) => {
                        info!(
                            "done with ChanAck step {} => {:#?}\n",
                            channel.dst_chain().id(),
                            event
                        );

                        return Ok(event);
                    }
                    IbcEvent::ChainError(e) => return Err(ChannelError::tx_response(e)),
                    _ => {}
                }
            }

            return Err(ChannelError::missing_event(
                "no chan ack event was in the response".to_string(),
            ));
        }

        do_build_chan_open_ack_and_send(self).map_err(|e| {
            error!("failed ChanAck {:?}: {}", self.b_side, e);
            e
        })
    }

    pub fn build_chan_open_confirm(&self) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        // Source and destination channel IDs must be specified
        let src_channel_id = self
            .src_channel_id()
            .ok_or_else(ChannelError::missing_local_channel_id)?;
        let dst_channel_id = self
            .dst_channel_id()
            .ok_or_else(ChannelError::missing_counterparty_channel_id)?;

        // Check that the destination chain will accept the message
        self.validated_expected_channel(ChannelMsgType::OpenConfirm)?;

        // Channel must exist on source
        self.src_chain()
            .query_channel(self.src_port_id(), src_channel_id, Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        // Connection must exist on destination
        self.dst_chain()
            .query_connection(self.dst_connection_id(), Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, query_height)
            .map_err(ChannelError::channel_proof)?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.map(|p| p.height()))?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ChannelError::fetch_signer(self.dst_chain().id().untag(), e))?;

        // Build the domain type message
        let new_msg =
            MsgChannelOpenConfirm::tagged_new(self.dst_port_id(), dst_channel_id, proofs, signer);

        msgs.push(new_msg.map_into(Msg::to_any));
        Ok(msgs)
    }

    pub fn build_chan_open_confirm_and_send(
        &self,
    ) -> Result<Tagged<ChainB, IbcEvent>, ChannelError> {
        fn do_build_chan_open_confirm_and_send<ChainA, ChainB>(
            channel: &Channel<ChainA, ChainB>,
        ) -> Result<Tagged<ChainB, IbcEvent>, ChannelError>
        where
            ChainA: ChainHandle<ChainB>,
            ChainB: ChainHandle<ChainA>,
        {
            let dst_msgs = channel.build_chan_open_confirm()?;

            let events = channel
                .dst_chain()
                .send_msgs(dst_msgs)
                .map_err(|e| ChannelError::submit(channel.dst_chain().id().untag(), e))?;

            for event in events {
                match event.value() {
                    IbcEvent::OpenConfirmChannel(_) => {
                        info!("done {} => {:#?}\n", channel.dst_chain().id(), event);
                        return Ok(event);
                    }
                    IbcEvent::ChainError(_) => {
                        return Err(ChannelError::invalid_event(event.untag()))
                    }
                    _ => {}
                }
            }

            return Err(ChannelError::missing_event(
                "no chan confirm event was in the response".to_string(),
            ));
        }

        do_build_chan_open_confirm_and_send(self).map_err(|e| {
            error!("failed ChanConfirm {:?}: {}", self.b_side, e);
            e
        })
    }

    pub fn build_chan_close_init(&self) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        // Destination channel ID must be specified
        let dst_channel_id = self
            .dst_channel_id()
            .ok_or_else(ChannelError::missing_counterparty_channel_id)?;

        // Channel must exist on destination
        self.dst_chain()
            .query_channel(self.dst_port_id(), dst_channel_id, Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ChannelError::fetch_signer(self.dst_chain().id().untag(), e))?;

        // Build the domain type message
        let new_msg = MsgChannelCloseInit::tagged_new(self.dst_port_id(), dst_channel_id, signer);

        Ok(vec![new_msg.map_into(Msg::to_any)])
    }

    pub fn build_chan_close_init_and_send(&self) -> Result<Tagged<ChainB, IbcEvent>, ChannelError> {
        let dst_msgs = self.build_chan_close_init()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::submit(self.dst_chain().id().untag(), e))?;

        // Find the relevant event for channel close init
        for event in events {
            match event.value() {
                IbcEvent::CloseInitChannel(_) => {
                    return Ok(event);
                }
                IbcEvent::ChainError(e) => return Err(ChannelError::tx_response(e.clone())),
                _ => {}
            }
        }

        Err(ChannelError::missing_event(
            "no chan init event was in the response".to_string(),
        ))
    }

    pub fn build_chan_close_confirm(&self) -> Result<Vec<Tagged<ChainB, Any>>, ChannelError> {
        // Source and destination channel IDs must be specified
        let src_channel_id = self
            .src_channel_id()
            .ok_or_else(ChannelError::missing_local_channel_id)?;

        let dst_channel_id = self
            .dst_channel_id()
            .ok_or_else(ChannelError::missing_counterparty_channel_id)?;

        // Check that the destination chain will accept the message
        self.validated_expected_channel(ChannelMsgType::CloseConfirm)?;

        // Channel must exist on source
        self.src_chain()
            .query_channel(self.src_port_id(), src_channel_id, Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        // Connection must exist on destination
        self.dst_chain()
            .query_connection(self.dst_connection_id(), Height::tagged_zero())
            .map_err(|e| ChannelError::query(self.dst_chain().id().untag(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::query(self.src_chain().id().untag(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), src_channel_id, query_height)
            .map_err(ChannelError::channel_proof)?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.map(|p| p.height()))?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ChannelError::fetch_signer(self.dst_chain().id().untag(), e))?;

        // Build the domain type message
        let new_msg =
            MsgChannelCloseConfirm::tagged_new(self.dst_port_id(), dst_channel_id, proofs, signer);

        msgs.push(new_msg.map_into(Msg::to_any));
        Ok(msgs)
    }

    pub fn build_chan_close_confirm_and_send(
        &self,
    ) -> Result<Tagged<ChainB, IbcEvent>, ChannelError> {
        let dst_msgs = self.build_chan_close_confirm()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::submit(self.dst_chain().id().untag(), e))?;

        // Find the relevant event for channel close confirm
        for event in events {
            match event.value() {
                IbcEvent::CloseConfirmChannel(_) => return Ok(event),
                IbcEvent::ChainError(e) => return Err(ChannelError::tx_response(e.clone())),
                _ => {}
            }
        }

        Err(ChannelError::missing_event(
            "no chan confirm event was in the response".to_string(),
        ))
    }
}

pub fn extract_channel_id(event: &IbcEvent) -> Result<ChannelId, ChannelError> {
    match event {
        IbcEvent::OpenInitChannel(ev) => ev.channel_id(),
        IbcEvent::OpenTryChannel(ev) => ev.channel_id(),
        IbcEvent::OpenAckChannel(ev) => ev.channel_id(),
        IbcEvent::OpenConfirmChannel(ev) => ev.channel_id(),
        _ => None,
    }
    .ok_or_else(|| ChannelError::missing_event("cannot extract channel_id from result".to_string()))
}

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
    CloseConfirm,
}

fn check_destination_channel_state<Chain, Counterparty>(
    channel_id: Tagged<Chain, ChannelId>,
    existing_channel: ChannelEnd<Chain, Counterparty>,
    expected_channel: ChannelEnd<Chain, Counterparty>,
) -> Result<(), ChannelError>
where
    Chain: ChainHandle<Counterparty>,
{
    let good_connection_hops =
        existing_channel.value().connection_hops() == expected_channel.value().connection_hops();

    // TODO: Refactor into a method
    let good_state =
        *existing_channel.value().state() as u32 <= *expected_channel.value().state() as u32;

    let good_channel_port_ids = existing_channel
        .value()
        .counterparty()
        .channel_id()
        .is_none()
        || existing_channel.value().counterparty().channel_id()
            == expected_channel.value().counterparty().channel_id()
            && existing_channel.value().counterparty().port_id()
                == expected_channel.value().counterparty().port_id();

    // TODO: Check versions

    if good_state && good_connection_hops && good_channel_port_ids {
        Ok(())
    } else {
        Err(ChannelError::channel_already_exist(channel_id.untag()))
    }
}
