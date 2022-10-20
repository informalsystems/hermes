use core::fmt::{Display, Error as FmtError, Formatter};
use core::time::Duration;
use std::thread;

use ibc_proto::google::protobuf::Any;
use serde::Serialize;
use tracing::{debug, error, info, warn};

use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, Counterparty, IdentifiedConnectionEnd, State,
};
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::timestamp::ZERO_DURATION;
use ibc_relayer_types::tx_msg::Msg;

use crate::chain::counterparty::connection_state_on_destination;
use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    IncludeProof, PageRequest, QueryConnectionRequest, QueryConnectionsRequest, QueryHeight,
};
use crate::chain::tracking::TrackedMsgs;
use crate::foreign_client::{ForeignClient, HasExpiredOrFrozenError};
use crate::object::Connection as WorkerConnectionObject;
use crate::util::pretty::{PrettyDuration, PrettyOption};
use crate::util::retry::{retry_with_index, RetryResult};
use crate::util::task::Next;

mod error;
pub use error::ConnectionError;

/// Maximum value allowed for packet delay on any new connection that the relayer establishes.
pub const MAX_PACKET_DELAY: Duration = Duration::from_secs(120);

mod handshake_retry {
    //! Provides utility methods and constants to configure the retry behavior
    //! for the connection handshake algorithm.

    use crate::connection::ConnectionError;
    use crate::util::retry::{clamp_total, ConstantGrowth};
    use core::time::Duration;

    /// Approximate number of retries per block.
    const PER_BLOCK_RETRIES: u32 = 10;

    /// Defines the increment in delay between subsequent retries.
    /// A value of `0` will make the retry delay constant.
    const DELAY_INCREMENT: u64 = 0;

    /// Maximum retry delay expressed in number of blocks
    const BLOCK_NUMBER_DELAY: u32 = 10;

    /// The default retry strategy.
    /// We retry with a constant backoff strategy. The strategy is parametrized by the
    /// maximum block time expressed as a `Duration`.
    pub fn default_strategy(max_block_times: Duration) -> impl Iterator<Item = Duration> {
        let retry_delay = max_block_times / PER_BLOCK_RETRIES;

        clamp_total(
            ConstantGrowth::new(retry_delay, Duration::from_secs(DELAY_INCREMENT)),
            retry_delay,
            max_block_times * BLOCK_NUMBER_DELAY,
        )
    }

    /// Translates from an error type that the `retry` mechanism threw into
    /// a crate specific error of [`ConnectionError`] type.
    pub fn from_retry_error(
        e: retry::Error<ConnectionError>,
        description: String,
    ) -> ConnectionError {
        ConnectionError::max_retry(description, e.tries, e.total_delay, e.error)
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(bound(serialize = "(): Serialize"))]
pub struct ConnectionSide<Chain: ChainHandle> {
    #[serde(skip)]
    pub(crate) chain: Chain,
    client_id: ClientId,
    connection_id: Option<ConnectionId>,
}

impl<Chain: ChainHandle> Display for ConnectionSide<Chain> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.connection_id {
            Some(connection_id) => write!(
                f,
                "ConnectionSide {{ chain: {}, client_id: {}, connection_id: {} }}",
                self.chain, self.client_id, connection_id
            ),
            None => write!(
                f,
                "ConnectionSide {{ chain: {}, client_id: {}, connection_id: None }}",
                self.chain, self.client_id
            ),
        }
    }
}

impl<Chain: ChainHandle> ConnectionSide<Chain> {
    pub fn new(chain: Chain, client_id: ClientId, connection_id: Option<ConnectionId>) -> Self {
        Self {
            chain,
            client_id,
            connection_id,
        }
    }

    pub fn connection_id(&self) -> Option<&ConnectionId> {
        self.connection_id.as_ref()
    }

    pub fn map_chain<ChainB: ChainHandle>(
        self,
        mapper: impl FnOnce(Chain) -> ChainB,
    ) -> ConnectionSide<ChainB> {
        ConnectionSide {
            chain: mapper(self.chain),
            client_id: self.client_id,
            connection_id: self.connection_id,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(bound(serialize = "(): Serialize"))]
pub struct Connection<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub delay_period: Duration,
    pub a_side: ConnectionSide<ChainA>,
    pub b_side: ConnectionSide<ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Display for Connection<ChainA, ChainB> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "Connection {{ delay_period: {}, a_side: {}, b_side: {} }}",
            PrettyDuration(&self.delay_period),
            self.a_side,
            self.b_side
        )
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Connection<ChainA, ChainB> {
    /// Create a new connection, ensuring that the handshake has succeeded and the two connection
    /// ends exist on each side.
    pub fn new(
        b_to_a_client: ForeignClient<ChainA, ChainB>,
        a_to_b_client: ForeignClient<ChainB, ChainA>,
        delay_period: Duration,
    ) -> Result<Self, ConnectionError> {
        Self::validate_clients(&b_to_a_client, &a_to_b_client)?;

        // Validate the delay period against the upper bound
        if delay_period > MAX_PACKET_DELAY {
            return Err(ConnectionError::max_delay_period(
                delay_period,
                MAX_PACKET_DELAY,
            ));
        }

        let mut c = Self {
            delay_period,
            a_side: ConnectionSide::new(
                b_to_a_client.dst_chain(),
                b_to_a_client.id().clone(),
                Default::default(),
            ),
            b_side: ConnectionSide::new(
                a_to_b_client.dst_chain(),
                a_to_b_client.id().clone(),
                Default::default(),
            ),
        };

        c.handshake()?;

        Ok(c)
    }

    pub fn restore_from_event(
        chain: ChainA,
        counterparty_chain: ChainB,
        connection_open_event: &IbcEvent,
    ) -> Result<Connection<ChainA, ChainB>, ConnectionError> {
        let connection_event_attributes = connection_open_event
            .connection_attributes()
            .ok_or_else(|| ConnectionError::invalid_event(connection_open_event.clone()))?;

        let connection_id = connection_event_attributes.connection_id.clone();

        let counterparty_connection_id = connection_event_attributes
            .counterparty_connection_id
            .clone();

        let client_id = connection_event_attributes.client_id.clone();
        let counterparty_client_id = connection_event_attributes.counterparty_client_id.clone();

        Ok(Connection {
            // The event does not include the connection delay.
            delay_period: Default::default(),
            a_side: ConnectionSide::new(chain, client_id, connection_id),
            b_side: ConnectionSide::new(
                counterparty_chain,
                counterparty_client_id,
                counterparty_connection_id,
            ),
        })
    }

    /// Recreates a 'Connection' object from the worker's object built from chain state scanning.
    /// The connection must exist on chain.
    pub fn restore_from_state(
        chain: ChainA,
        counterparty_chain: ChainB,
        connection: WorkerConnectionObject,
        height: Height,
    ) -> Result<(Connection<ChainA, ChainB>, State), ConnectionError> {
        let (a_connection, _) = chain
            .query_connection(
                QueryConnectionRequest {
                    connection_id: connection.src_connection_id.clone(),
                    height: QueryHeight::Specific(height),
                },
                IncludeProof::No,
            )
            .map_err(ConnectionError::relayer)?;

        let client_id = a_connection.client_id();
        let delay_period = a_connection.delay_period();

        let counterparty_connection_id = a_connection.counterparty().connection_id.clone();

        let counterparty_client_id = a_connection.counterparty().client_id();

        let mut handshake_connection = Connection {
            delay_period,
            a_side: ConnectionSide::new(
                chain,
                client_id.clone(),
                Some(connection.src_connection_id.clone()),
            ),
            b_side: ConnectionSide::new(
                counterparty_chain.clone(),
                counterparty_client_id.clone(),
                counterparty_connection_id.clone(),
            ),
        };

        if a_connection.state_matches(&State::Init) && counterparty_connection_id.is_none() {
            let connections: Vec<IdentifiedConnectionEnd> = counterparty_chain
                .query_connections(QueryConnectionsRequest {
                    pagination: Some(PageRequest::all()),
                })
                .map_err(ConnectionError::relayer)?;

            for conn in connections {
                if !conn
                    .connection_end
                    .client_id_matches(a_connection.counterparty().client_id())
                {
                    continue;
                }
                if let Some(remote_connection_id) =
                    conn.connection_end.counterparty().connection_id()
                {
                    if remote_connection_id == &connection.src_connection_id {
                        handshake_connection.b_side.connection_id = Some(conn.connection_id);
                        break;
                    }
                }
            }
        }

        Ok((handshake_connection, *a_connection.state()))
    }

    pub fn find(
        a_client: ForeignClient<ChainA, ChainB>,
        b_client: ForeignClient<ChainB, ChainA>,
        conn_end_a: &IdentifiedConnectionEnd,
    ) -> Result<Connection<ChainA, ChainB>, ConnectionError> {
        Self::validate_clients(&a_client, &b_client)?;

        // Validate the connection end
        if conn_end_a.end().client_id().ne(a_client.id()) {
            return Err(ConnectionError::connection_client_id_mismatch(
                conn_end_a.end().client_id().clone(),
                a_client.id().clone(),
            ));
        }
        if conn_end_a.end().counterparty().client_id() != b_client.id() {
            return Err(ConnectionError::connection_client_id_mismatch(
                conn_end_a.end().counterparty().client_id().clone(),
                b_client.id().clone(),
            ));
        }
        if !conn_end_a.end().state_matches(&State::Open) {
            return Err(ConnectionError::connection_not_open(
                *conn_end_a.end().state(),
            ));
        }
        let b_conn_id = conn_end_a
            .end()
            .counterparty()
            .connection_id()
            .cloned()
            .ok_or_else(|| {
                ConnectionError::missing_counterparty_connection_id_field(
                    conn_end_a.end().counterparty().clone(),
                )
            })?;

        let c = Connection {
            delay_period: conn_end_a.end().delay_period(),
            a_side: ConnectionSide {
                chain: a_client.dst_chain.clone(),
                client_id: a_client.id,
                connection_id: Some(conn_end_a.id().clone()),
            },
            b_side: ConnectionSide {
                chain: b_client.dst_chain.clone(),
                client_id: b_client.id,
                connection_id: Some(b_conn_id),
            },
        };

        Ok(c)
    }

    // Verifies that the two clients are mutually consistent, i.e., they serve the same two chains.
    fn validate_clients(
        a_client: &ForeignClient<ChainA, ChainB>,
        b_client: &ForeignClient<ChainB, ChainA>,
    ) -> Result<(), ConnectionError> {
        if a_client.src_chain().id() != b_client.dst_chain().id() {
            return Err(ConnectionError::chain_id_mismatch(
                a_client.src_chain().id(),
                b_client.dst_chain().id(),
            ));
        }

        if a_client.dst_chain().id() != b_client.src_chain().id() {
            return Err(ConnectionError::chain_id_mismatch(
                a_client.dst_chain().id(),
                b_client.src_chain().id(),
            ));
        }

        Ok(())
    }

    pub fn src_chain(&self) -> ChainA {
        self.a_side.chain.clone()
    }

    pub fn dst_chain(&self) -> ChainB {
        self.b_side.chain.clone()
    }

    pub fn a_chain(&self) -> ChainA {
        self.a_side.chain.clone()
    }

    pub fn b_chain(&self) -> ChainB {
        self.b_side.chain.clone()
    }

    pub fn src_client_id(&self) -> &ClientId {
        &self.a_side.client_id
    }

    pub fn dst_client_id(&self) -> &ClientId {
        &self.b_side.client_id
    }

    pub fn src_connection_id(&self) -> Option<&ConnectionId> {
        self.a_side.connection_id()
    }

    pub fn dst_connection_id(&self) -> Option<&ConnectionId> {
        self.b_side.connection_id()
    }

    pub fn a_connection_id(&self) -> Option<&ConnectionId> {
        self.a_side.connection_id()
    }
    pub fn b_connection_id(&self) -> Option<&ConnectionId> {
        self.b_side.connection_id()
    }

    fn a_connection(
        &self,
        connection_id: Option<&ConnectionId>,
    ) -> Result<ConnectionEnd, ConnectionError> {
        if let Some(id) = connection_id {
            self.a_chain()
                .query_connection(
                    QueryConnectionRequest {
                        connection_id: id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map(|(connection_end, _)| connection_end)
                .map_err(|e| ConnectionError::chain_query(self.a_chain().id(), e))
        } else {
            Ok(ConnectionEnd::default())
        }
    }

    fn b_connection(
        &self,
        connection_id: Option<&ConnectionId>,
    ) -> Result<ConnectionEnd, ConnectionError> {
        if let Some(id) = connection_id {
            self.b_chain()
                .query_connection(
                    QueryConnectionRequest {
                        connection_id: id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map(|(connection_end, _)| connection_end)
                .map_err(|e| ConnectionError::chain_query(self.b_chain().id(), e))
        } else {
            Ok(ConnectionEnd::default())
        }
    }

    /// Returns a `Duration` representing the maximum value among the
    /// [`ChainConfig.max_block_time`] for the two networks that
    /// this connection belongs to.
    fn max_block_times(&self) -> Result<Duration, ConnectionError> {
        let a_block_time = self
            .a_chain()
            .config()
            .map_err(ConnectionError::relayer)?
            .max_block_time;
        let b_block_time = self
            .b_chain()
            .config()
            .map_err(ConnectionError::relayer)?
            .max_block_time;
        Ok(a_block_time.max(b_block_time))
    }

    pub fn flipped(&self) -> Connection<ChainB, ChainA> {
        Connection {
            a_side: self.b_side.clone(),
            b_side: self.a_side.clone(),
            delay_period: self.delay_period,
        }
    }

    /// Queries the chains for latest connection end information. It verifies the relayer connection
    /// IDs and updates them if needed.
    /// Returns the states of the two connection ends.
    ///
    /// The relayer connection stores the connection identifiers on the two chains a and b.
    /// These identifiers need to be cross validated with the corresponding on-chain ones at some
    /// handshake steps.
    /// This is required because of crossing handshake messages in the presence of multiple relayers.
    ///
    /// Chain a is queried with the relayer's `a_side.connection_id` (`relayer_a_id`) with result
    /// `a_connection`. If the counterparty id of this connection, `a_counterparty_id`,
    /// is some id then it must match the relayer's `b_side.connection_id` (`relayer_b_id`).
    /// A similar check is done for the `b_side` of the connection.
    ///
    ///  a                                 relayer                                    b
    ///  |                     a_side -- connection -- b_side                         |
    ///  a_id _____________> relayer_a_id             relayer_b_id <______________> b_id
    ///  |                      \                                /                    |
    /// a_counterparty_id <_____________________________________/                     |
    ///                           \____________________________________>   b_counterparty_id
    ///
    /// Case 1 (fix connection ID):
    ///  a                                                      b
    ///  | <-- Init (r1)                                        |
    ///  | a_id = 1, a_counterparty_id = None                   |
    ///  |                                         Try (r2) --> |
    ///  |                    b_id = 100, b_counterparty_id = 1 |
    ///  |                                         Try (r1) --> |
    ///  |                    b_id = 101, b_counterparty_id = 1 |
    ///  | <-- Ack (r2)
    ///  | a_id = 1, a_counterparty_id = 100
    ///
    /// Here relayer r1 has a_side connection 1 and b_side connection 101
    /// while on chain a the counterparty of connection 1 is 100. r1 needs to update
    /// its b_side to 100
    ///
    /// Case 2 (update from None to some connection ID):
    ///  a                                                      b
    ///  | <-- Init (r1)                                        |
    ///  | a_id = 1, a_counterparty_id = None                   |
    ///  |                                         Try (r2) --> |
    ///  |                    b_id = 100, b_counterparty_id = 1 |
    ///  | <-- Ack (r2)
    ///  | a_id = 1, a_counterparty_id = 100
    ///
    /// Here relayer r1 has a_side connection 1 and b_side is unknown
    /// while on chain a the counterparty of connection 1 is 100. r1 needs to update
    /// its b_side to 100
    fn update_connection_and_query_states(&mut self) -> Result<(State, State), ConnectionError> {
        let relayer_a_id = self.a_side.connection_id();
        let relayer_b_id = self.b_side.connection_id().cloned();

        let a_connection = self.a_connection(relayer_a_id)?;
        let a_counterparty_id = a_connection.counterparty().connection_id();

        if a_counterparty_id.is_some() && a_counterparty_id != relayer_b_id.as_ref() {
            warn!(
                "updating the expected {} of side_b({}) since it is different than the \
                counterparty of {}: {}, on {}. This is typically caused by crossing handshake \
                messages in the presence of multiple relayers.",
                PrettyOption(&relayer_b_id),
                self.b_chain().id(),
                PrettyOption(&relayer_a_id),
                PrettyOption(&a_counterparty_id),
                self.a_chain().id(),
            );
            self.b_side.connection_id = a_counterparty_id.cloned();
        }

        let updated_relayer_b_id = self.b_side.connection_id();
        let b_connection = self.b_connection(updated_relayer_b_id)?;
        let b_counterparty_id = b_connection.counterparty().connection_id();

        if b_counterparty_id.is_some() && b_counterparty_id != relayer_a_id {
            if updated_relayer_b_id == relayer_b_id.as_ref() {
                warn!(
                    "updating the expected {} of side_a({}) since it is different than the \
                    counterparty of {}: {}, on {}. This is typically caused by crossing handshake \
                    messages in the presence of multiple relayers.",
                    PrettyOption(&relayer_a_id),
                    self.a_chain().id(),
                    PrettyOption(&updated_relayer_b_id),
                    PrettyOption(&b_counterparty_id),
                    self.b_chain().id(),
                );
                self.a_side.connection_id = b_counterparty_id.cloned();
            } else {
                panic!(
                    "mismatched connection ids in connection ends: {} - {:?} and {} - {:?}",
                    self.a_chain().id(),
                    a_connection,
                    self.b_chain().id(),
                    b_connection,
                );
            }
        }
        Ok((*a_connection.state(), *b_connection.state()))
    }

    /// Sends a connection open handshake message.
    /// The message sent depends on the chain status of the connection ends.
    fn do_conn_open_handshake(&mut self) -> Result<(), ConnectionError> {
        let (a_state, b_state) = self.update_connection_and_query_states()?;
        debug!(
            "do_conn_open_handshake with connection end states: {}, {}",
            a_state, b_state
        );

        match (a_state, b_state) {
            // send the Init message to chain a (source)
            (State::Uninitialized, State::Uninitialized) => {
                let event = self.flipped().build_conn_init_and_send().map_err(|e| {
                    error!("failed ConnOpenInit {}: {}", self.a_side, e);
                    e
                })?;
                let connection_id = extract_connection_id(&event)?;
                self.a_side.connection_id = Some(connection_id.clone());
            }

            // send the Try message to chain a (source)
            (State::Uninitialized, State::Init) | (State::Init, State::Init) => {
                let event = self.flipped().build_conn_try_and_send().map_err(|e| {
                    error!("failed ConnOpenTry {}: {}", self.a_side, e);
                    e
                })?;

                let connection_id = extract_connection_id(&event)?;
                self.a_side.connection_id = Some(connection_id.clone());
            }

            // send the Try message to chain b (destination)
            (State::Init, State::Uninitialized) => {
                let event = self.build_conn_try_and_send().map_err(|e| {
                    error!("failed ConnOpenTry {}: {}", self.b_side, e);
                    e
                })?;

                let connection_id = extract_connection_id(&event)?;
                self.b_side.connection_id = Some(connection_id.clone());
            }

            // send the Ack message to chain a (source)
            (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                self.flipped().build_conn_ack_and_send().map_err(|e| {
                    error!("failed ConnOpenAck {}: {}", self.a_side, e);
                    e
                })?;
            }

            // send the Ack message to chain b (destination)
            (State::TryOpen, State::Init) => {
                self.build_conn_ack_and_send().map_err(|e| {
                    error!("failed ConnOpenAck {}: {}", self.b_side, e);
                    e
                })?;
            }

            // send the Confirm message to chain b (destination)
            (State::Open, State::TryOpen) => {
                self.build_conn_confirm_and_send().map_err(|e| {
                    error!("failed ConnOpenConfirm {}: {}", self.b_side, e);
                    e
                })?;
            }

            // send the Confirm message to chain a (source)
            (State::TryOpen, State::Open) => {
                self.flipped().build_conn_confirm_and_send().map_err(|e| {
                    error!("failed ConnOpenConfirm {}: {}", self.a_side, e);
                    e
                })?;
            }

            (State::Open, State::Open) => {
                info!("connection handshake already finished for {}", self);
                return Ok(());
            }

            (a_state, b_state) => {
                warn!(
                    "do_conn_open_handshake does not handle connection end state combination: \
                    {}-{}, {}-{}. will retry to account for RPC node data availability issues.",
                    self.a_chain().id(),
                    a_state,
                    self.b_chain().id(),
                    b_state
                );
            }
        }
        Err(ConnectionError::handshake_finalize())
    }

    /// Executes the connection handshake protocol (ICS003)
    fn handshake(&mut self) -> Result<(), ConnectionError> {
        let max_block_times = self.max_block_times()?;

        retry_with_index(handshake_retry::default_strategy(max_block_times), |_| {
            if let Err(e) = self.do_conn_open_handshake() {
                if e.is_expired_or_frozen_error() {
                    RetryResult::Err(e)
                } else {
                    RetryResult::Retry(e)
                }
            } else {
                RetryResult::Ok(())
            }
        })
        .map_err(|err| {
            error!("failed to open connection after {} retries", err.tries);

            handshake_retry::from_retry_error(
                err,
                format!("failed to finish connection handshake for {:?}", self),
            )
        })?;

        Ok(())
    }

    pub fn counterparty_state(&self) -> Result<State, ConnectionError> {
        // Source connection ID must be specified
        let connection_id = self
            .src_connection_id()
            .ok_or_else(ConnectionError::missing_local_connection_id)?;

        let (connection_end, _) = self
            .src_chain()
            .query_connection(
                QueryConnectionRequest {
                    connection_id: connection_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(|e| ConnectionError::connection_query(connection_id.clone(), e))?;

        let connection = IdentifiedConnectionEnd {
            connection_end,
            connection_id: connection_id.clone(),
        };

        connection_state_on_destination(&connection, &self.dst_chain())
            .map_err(ConnectionError::supervisor)
    }

    pub fn handshake_step(
        &mut self,
        state: State,
    ) -> Result<(Option<IbcEvent>, Next), ConnectionError> {
        let event = match (state, self.counterparty_state()?) {
            (State::Init, State::Uninitialized) => Some(self.build_conn_try_and_send()?),
            (State::Init, State::Init) => Some(self.build_conn_try_and_send()?),
            (State::TryOpen, State::Init) => Some(self.build_conn_ack_and_send()?),
            (State::TryOpen, State::TryOpen) => Some(self.build_conn_ack_and_send()?),
            (State::Open, State::TryOpen) => Some(self.build_conn_confirm_and_send()?),
            (State::Open, State::Open) => return Ok((None, Next::Abort)),

            // If the counterparty state is already Open but current state is TryOpen,
            // return anyway as the final step is to be done by the counterparty worker.
            (State::TryOpen, State::Open) => return Ok((None, Next::Abort)),

            _ => None,
        };

        // Abort if the connection is at OpenAck or OpenConfirm stage, as there is nothing more for the worker to do
        match event {
            Some(IbcEvent::OpenConfirmConnection(_)) | Some(IbcEvent::OpenAckConnection(_)) => {
                Ok((event, Next::Abort))
            }
            _ => Ok((event, Next::Continue)),
        }
    }

    pub fn step_state(&mut self, state: State, index: u64) -> RetryResult<Next, u64> {
        match self.handshake_step(state) {
            Err(e) => {
                if e.is_expired_or_frozen_error() {
                    error!(
                        "failed to establish connection handshake on frozen client: {}",
                        e
                    );
                    RetryResult::Err(index)
                } else {
                    error!("failed {} with error {}", state, e);
                    RetryResult::Retry(index)
                }
            }
            Ok((Some(ev), handshake_completed)) => {
                info!("connection handshake step completed with events: {}", ev);
                RetryResult::Ok(handshake_completed)
            }
            Ok((None, handshake_completed)) => RetryResult::Ok(handshake_completed),
        }
    }

    pub fn step_event(&mut self, event: &IbcEvent, index: u64) -> RetryResult<Next, u64> {
        let state = match event {
            IbcEvent::OpenInitConnection(_) => State::Init,
            IbcEvent::OpenTryConnection(_) => State::TryOpen,
            IbcEvent::OpenAckConnection(_) => State::Open,
            IbcEvent::OpenConfirmConnection(_) => State::Open,
            _ => State::Uninitialized,
        };

        self.step_state(state, index)
    }

    /// Retrieves the connection from destination and compares against the expected connection
    /// built from the message type (`msg_type`) and options (`opts`).
    /// If the expected and the destination connections are compatible, it returns the expected connection.
    fn validated_expected_connection(
        &self,
        msg_type: ConnectionMsgType,
    ) -> Result<ConnectionEnd, ConnectionError> {
        let dst_connection_id = self
            .dst_connection_id()
            .ok_or_else(ConnectionError::missing_counterparty_connection_id)?;

        let prefix = self
            .src_chain()
            .query_commitment_prefix()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        // If there is a connection present on the destination chain, it should look like this:
        let counterparty = Counterparty::new(
            self.src_client_id().clone(),
            self.src_connection_id().cloned(),
            prefix,
        );

        // The highest expected state, depends on the message type:
        let highest_state = match msg_type {
            ConnectionMsgType::OpenAck => State::TryOpen,
            ConnectionMsgType::OpenConfirm => State::TryOpen,
            _ => State::Uninitialized,
        };

        let versions = self
            .src_chain()
            .query_compatible_versions()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        let dst_expected_connection = ConnectionEnd::new(
            highest_state,
            self.dst_client_id().clone(),
            counterparty,
            versions,
            ZERO_DURATION,
        );

        // Retrieve existing connection if any
        let (dst_connection, _) = self
            .dst_chain()
            .query_connection(
                QueryConnectionRequest {
                    connection_id: dst_connection_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(|e| ConnectionError::chain_query(self.dst_chain().id(), e))?;

        // Check if a connection is expected to exist on destination chain
        // A connection must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dst_connection.state_matches(&State::Uninitialized) {
            return Err(ConnectionError::missing_connection_id(
                self.dst_chain().id(),
            ));
        }

        check_destination_connection_state(
            dst_connection_id.clone(),
            dst_connection,
            dst_expected_connection.clone(),
        )?;

        Ok(dst_expected_connection)
    }

    pub fn build_update_client_on_src(&self, height: Height) -> Result<Vec<Any>, ConnectionError> {
        let client = self.restore_src_client();
        client.wait_and_build_update_client(height).map_err(|e| {
            ConnectionError::client_operation(
                self.src_client_id().clone(),
                self.src_chain().id(),
                e,
            )
        })
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, ConnectionError> {
        let client = self.restore_dst_client();
        client.wait_and_build_update_client(height).map_err(|e| {
            ConnectionError::client_operation(
                self.dst_client_id().clone(),
                self.dst_chain().id(),
                e,
            )
        })
    }

    pub fn build_conn_init(&self) -> Result<Vec<Any>, ConnectionError> {
        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ConnectionError::signer(self.dst_chain().id(), e))?;

        let prefix = self
            .src_chain()
            .query_commitment_prefix()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        let counterparty = Counterparty::new(self.src_client_id().clone(), None, prefix);

        let version = self
            .dst_chain()
            .query_compatible_versions()
            .map_err(|e| ConnectionError::chain_query(self.dst_chain().id(), e))?[0]
            .clone();

        // Build the domain type message
        let new_msg = MsgConnectionOpenInit {
            client_id: self.dst_client_id().clone(),
            counterparty,
            version: Some(version),
            delay_period: self.delay_period,
            signer,
        };

        Ok(vec![new_msg.to_any()])
    }

    pub fn build_conn_init_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let dst_msgs = self.build_conn_init()?;

        let tm = TrackedMsgs::new_static(dst_msgs, "ConnectionOpenInit");

        let events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| ConnectionError::submit(self.dst_chain().id(), e))?;

        // Find the relevant event for connection init
        let result = events
            .into_iter()
            .find(|event_with_height| {
                matches!(event_with_height.event, IbcEvent::OpenInitConnection(_))
                    || matches!(event_with_height.event, IbcEvent::ChainError(_))
            })
            .ok_or_else(ConnectionError::missing_connection_init_event)?;

        // TODO - make chainError an actual error
        match &result.event {
            IbcEvent::OpenInitConnection(_) => {
                info!("🥂 {} => {}", self.dst_chain().id(), result);
                Ok(result.event)
            }
            IbcEvent::ChainError(e) => Err(ConnectionError::tx_response(e.clone())),
            _ => Err(ConnectionError::invalid_event(result.event)),
        }
    }

    /// Wait for the application on destination chain to advance beyond `consensus_height`.
    fn wait_for_dest_app_height_higher_than_consensus_proof_height(
        &self,
        consensus_height: Height,
    ) -> Result<(), ConnectionError> {
        let dst_application_latest_height = || {
            self.dst_chain()
                .query_latest_height()
                .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))
        };

        while consensus_height >= dst_application_latest_height()? {
            warn!(
                "client consensus proof height too high, \
                 waiting for destination chain to advance beyond {}",
                consensus_height
            );

            thread::sleep(Duration::from_millis(500));
        }

        Ok(())
    }

    /// Attempts to build a MsgConnOpenTry.
    ///
    /// Return the messages and the app height the destination chain must reach
    /// before we send the messages.
    pub fn build_conn_try(&self) -> Result<(Vec<Any>, Height), ConnectionError> {
        let src_connection_id = self
            .src_connection_id()
            .ok_or_else(ConnectionError::missing_local_connection_id)?;

        let (src_connection, _) = self
            .src_chain()
            .query_connection(
                QueryConnectionRequest {
                    connection_id: src_connection_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        // TODO - check that the src connection is consistent with the try options

        // Cross-check the delay_period
        let delay = if src_connection.delay_period() != self.delay_period {
            warn!("`delay_period` for ConnectionEnd @{} is {}s; delay period on local Connection object is set to {}s",
                self.src_chain().id(), src_connection.delay_period().as_secs_f64(), self.delay_period.as_secs_f64());

            warn!(
                "Overriding delay period for local connection object to {}s",
                src_connection.delay_period().as_secs_f64()
            );

            src_connection.delay_period()
        } else {
            self.delay_period
        };

        // Build add send the message(s) for updating client on source
        // TODO - add check if update client is required
        let src_client_target_height = self
            .dst_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::chain_query(self.dst_chain().id(), e))?;
        let client_msgs = self.build_update_client_on_src(src_client_target_height)?;

        let tm =
            TrackedMsgs::new_static(client_msgs, "update client on source for ConnectionOpenTry");
        self.src_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| ConnectionError::submit(self.src_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;
        let (client_state, proofs) = self
            .src_chain()
            .build_connection_proofs_and_client_state(
                ConnectionMsgType::OpenTry,
                src_connection_id,
                self.src_client_id(),
                query_height,
            )
            .map_err(ConnectionError::connection_proof)?;

        // Build message(s) for updating client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        let counterparty_versions = if src_connection.versions().is_empty() {
            self.src_chain()
                .query_compatible_versions()
                .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?
        } else {
            src_connection.versions().to_vec()
        };

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ConnectionError::signer(self.dst_chain().id(), e))?;

        let prefix = self
            .src_chain()
            .query_commitment_prefix()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        let counterparty = Counterparty::new(
            self.src_client_id().clone(),
            self.src_connection_id().cloned(),
            prefix,
        );

        let previous_connection_id = if src_connection.counterparty().connection_id.is_none() {
            self.b_side.connection_id.clone()
        } else {
            src_connection.counterparty().connection_id.clone()
        };

        let new_msg = MsgConnectionOpenTry {
            client_id: self.dst_client_id().clone(),
            client_state: client_state.map(Into::into),
            previous_connection_id,
            counterparty,
            counterparty_versions,
            proofs,
            delay_period: delay,
            signer,
        };

        msgs.push(new_msg.to_any());

        Ok((msgs, src_client_target_height))
    }

    pub fn build_conn_try_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let (dst_msgs, src_client_target_height) = self.build_conn_try()?;

        // Wait for the height of the application on the destination chain to be higher than
        // the height of the consensus state included in the proofs.
        self.wait_for_dest_app_height_higher_than_consensus_proof_height(src_client_target_height)?;

        let tm = TrackedMsgs::new_static(dst_msgs, "ConnectionOpenTry");

        let events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| ConnectionError::submit(self.dst_chain().id(), e))?;

        // Find the relevant event for connection try transaction
        let result = events
            .into_iter()
            .find(|event_with_height| {
                matches!(event_with_height.event, IbcEvent::OpenTryConnection(_))
                    || matches!(event_with_height.event, IbcEvent::ChainError(_))
            })
            .ok_or_else(ConnectionError::missing_connection_try_event)?;

        match &result.event {
            IbcEvent::OpenTryConnection(_) => {
                info!("🥂 {} => {}", self.dst_chain().id(), result);
                Ok(result.event)
            }
            IbcEvent::ChainError(e) => Err(ConnectionError::tx_response(e.clone())),
            _ => Err(ConnectionError::invalid_event(result.event)),
        }
    }

    /// Attempts to build a MsgConnOpenAck.
    ///
    /// Return the messages and the app height the destination chain must reach
    /// before we send the messages.
    pub fn build_conn_ack(&self) -> Result<(Vec<Any>, Height), ConnectionError> {
        let src_connection_id = self
            .src_connection_id()
            .ok_or_else(ConnectionError::missing_local_connection_id)?;
        let dst_connection_id = self
            .dst_connection_id()
            .ok_or_else(ConnectionError::missing_counterparty_connection_id)?;

        let _expected_dst_connection =
            self.validated_expected_connection(ConnectionMsgType::OpenAck)?;

        let (src_connection, _) = self
            .src_chain()
            .query_connection(
                QueryConnectionRequest {
                    connection_id: src_connection_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        // TODO - check that the src connection is consistent with the ack options

        // Build add **send** the message(s) for updating client on source.
        // TODO - add check if it is required
        let src_client_target_height = self
            .dst_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::chain_query(self.dst_chain().id(), e))?;

        let client_msgs = self.build_update_client_on_src(src_client_target_height)?;

        let tm =
            TrackedMsgs::new_static(client_msgs, "update client on source for ConnectionOpenAck");

        self.src_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| ConnectionError::submit(self.src_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        let (client_state, proofs) = self
            .src_chain()
            .build_connection_proofs_and_client_state(
                ConnectionMsgType::OpenAck,
                src_connection_id,
                self.src_client_id(),
                query_height,
            )
            .map_err(ConnectionError::connection_proof)?;

        // Build message(s) for updating client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ConnectionError::signer(self.dst_chain().id(), e))?;

        let new_msg = MsgConnectionOpenAck {
            connection_id: dst_connection_id.clone(),
            counterparty_connection_id: src_connection_id.clone(),
            client_state: client_state.map(Into::into),
            proofs,
            version: src_connection.versions()[0].clone(),
            signer,
        };

        msgs.push(new_msg.to_any());

        Ok((msgs, src_client_target_height))
    }

    pub fn build_conn_ack_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let (dst_msgs, src_client_target_height) = self.build_conn_ack()?;

        // Wait for the height of the application on the destination chain to be higher than
        // the height of the consensus state included in the proofs.
        self.wait_for_dest_app_height_higher_than_consensus_proof_height(src_client_target_height)?;

        let tm = TrackedMsgs::new_static(dst_msgs, "ConnectionOpenAck");

        let events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| ConnectionError::submit(self.dst_chain().id(), e))?;

        // Find the relevant event for connection ack
        let result = events
            .into_iter()
            .find(|event_with_height| {
                matches!(event_with_height.event, IbcEvent::OpenAckConnection(_))
                    || matches!(event_with_height.event, IbcEvent::ChainError(_))
            })
            .ok_or_else(ConnectionError::missing_connection_ack_event)?;

        match &result.event {
            IbcEvent::OpenAckConnection(_) => {
                info!("🥂 {} => {}", self.dst_chain().id(), result);
                Ok(result.event)
            }
            IbcEvent::ChainError(e) => Err(ConnectionError::tx_response(e.clone())),
            _ => Err(ConnectionError::invalid_event(result.event)),
        }
    }

    /// Attempts to build a MsgConnOpenConfirm.
    pub fn build_conn_confirm(&self) -> Result<Vec<Any>, ConnectionError> {
        let src_connection_id = self
            .src_connection_id()
            .ok_or_else(ConnectionError::missing_local_connection_id)?;
        let dst_connection_id = self
            .dst_connection_id()
            .ok_or_else(ConnectionError::missing_counterparty_connection_id)?;

        let _expected_dst_connection =
            self.validated_expected_connection(ConnectionMsgType::OpenAck)?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::chain_query(self.src_chain().id(), e))?;

        let (_src_connection, _) = self
            .src_chain()
            .query_connection(
                QueryConnectionRequest {
                    connection_id: src_connection_id.clone(),
                    height: QueryHeight::Specific(query_height),
                },
                IncludeProof::No,
            )
            .map_err(|e| ConnectionError::connection_query(src_connection_id.clone(), e))?;

        // TODO - check that the src connection is consistent with the confirm options

        let (_, proofs) = self
            .src_chain()
            .build_connection_proofs_and_client_state(
                ConnectionMsgType::OpenConfirm,
                src_connection_id,
                self.src_client_id(),
                query_height,
            )
            .map_err(ConnectionError::connection_proof)?;

        // Build message(s) for updating client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| ConnectionError::signer(self.dst_chain().id(), e))?;

        let new_msg = MsgConnectionOpenConfirm {
            connection_id: dst_connection_id.clone(),
            proofs,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_conn_confirm_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let dst_msgs = self.build_conn_confirm()?;

        let tm = TrackedMsgs::new_static(dst_msgs, "ConnectionOpenConfirm");

        let events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| ConnectionError::submit(self.dst_chain().id(), e))?;

        // Find the relevant event for connection confirm
        let result = events
            .into_iter()
            .find(|event_with_height| {
                matches!(event_with_height.event, IbcEvent::OpenConfirmConnection(_))
                    || matches!(event_with_height.event, IbcEvent::ChainError(_))
            })
            .ok_or_else(ConnectionError::missing_connection_confirm_event)?;

        match &result.event {
            IbcEvent::OpenConfirmConnection(_) => {
                info!("🥂 {} => {}", self.dst_chain().id(), result);
                Ok(result.event)
            }
            IbcEvent::ChainError(e) => Err(ConnectionError::tx_response(e.clone())),
            _ => Err(ConnectionError::invalid_event(result.event)),
        }
    }

    fn restore_src_client(&self) -> ForeignClient<ChainA, ChainB> {
        ForeignClient::restore(
            self.src_client_id().clone(),
            self.src_chain(),
            self.dst_chain(),
        )
    }

    fn restore_dst_client(&self) -> ForeignClient<ChainB, ChainA> {
        ForeignClient::restore(
            self.dst_client_id().clone(),
            self.dst_chain(),
            self.src_chain(),
        )
    }

    pub fn map_chain<ChainC: ChainHandle, ChainD: ChainHandle>(
        self,
        mapper_a: impl Fn(ChainA) -> ChainC,
        mapper_b: impl Fn(ChainB) -> ChainD,
    ) -> Connection<ChainC, ChainD> {
        Connection {
            delay_period: self.delay_period,
            a_side: self.a_side.map_chain(mapper_a),
            b_side: self.b_side.map_chain(mapper_b),
        }
    }
}

pub fn extract_connection_id(event: &IbcEvent) -> Result<&ConnectionId, ConnectionError> {
    match event {
        IbcEvent::OpenInitConnection(ev) => ev.connection_id(),
        IbcEvent::OpenTryConnection(ev) => ev.connection_id(),
        IbcEvent::OpenAckConnection(ev) => ev.connection_id(),
        IbcEvent::OpenConfirmConnection(ev) => ev.connection_id(),
        _ => None,
    }
    .ok_or_else(ConnectionError::missing_connection_id_from_event)
}

/// Enumeration of proof carrying ICS3 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConnectionMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
}

/// Verify that the destination connection exhibits the expected state.
fn check_destination_connection_state(
    connection_id: ConnectionId,
    existing_connection: ConnectionEnd,
    expected_connection: ConnectionEnd,
) -> Result<(), ConnectionError> {
    let good_client_ids = existing_connection.client_id() == expected_connection.client_id()
        && existing_connection.counterparty().client_id()
            == expected_connection.counterparty().client_id();

    let good_state = *existing_connection.state() as u32 <= *expected_connection.state() as u32;

    let good_connection_ids = existing_connection.counterparty().connection_id().is_none()
        || existing_connection.counterparty().connection_id()
            == expected_connection.counterparty().connection_id();

    let good_version = existing_connection.versions() == expected_connection.versions();

    let good_counterparty_prefix =
        existing_connection.counterparty().prefix() == expected_connection.counterparty().prefix();

    if good_state
        && good_client_ids
        && good_connection_ids
        && good_version
        && good_counterparty_prefix
    {
        Ok(())
    } else {
        Err(ConnectionError::connection_already_exists(connection_id))
    }
}
