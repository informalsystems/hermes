use std::time::Duration;

use prost_types::Any;
use serde::Serialize;
use thiserror::Error;
use tracing::{error, warn};

use ibc::events::IbcEvent;
use ibc::ics02_client::height::Height;
use ibc::ics03_connection::connection::{
    ConnectionEnd, Counterparty, IdentifiedConnectionEnd, State,
};
use ibc::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::timestamp::ZERO_DURATION;
use ibc::tx_msg::Msg;

use crate::chain::handle::ChainHandle;
use crate::error::Error;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::util::retry::RetryableError;

/// Maximum value allowed for packet delay on any new connection that the relayer establishes.
pub const MAX_PACKET_DELAY: Duration = Duration::from_secs(120);

const MAX_RETRIES: usize = 5;

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Error)]
pub enum ConnectionError {
    #[error("failed with underlying cause: {0}")]
    Failed(String),

    #[error("connection constructor error: {0}")]
    ConstructorFailed(String),

    #[error("failed during a query to chain id {0} due to underlying error: {1}")]
    QueryError(ChainId, Error),

    #[error("failed during an operation on client ({0}) hosted by chain ({1}) with error {2}")]
    ClientOperation(ClientId, ChainId, ForeignClientError),

    #[error(
        "failed during a transaction submission step to chain id {0} with underlying error: {1}"
    )]
    SubmitError(ChainId, Error),
}

impl RetryableError for ConnectionError {
    #[allow(clippy::match_like_matches_macro)]
    fn is_retryable(&self) -> bool {
        match self {
            ConnectionError::ClientOperation(_, _, e) => e.is_retryable(),

            // TODO: actually classify the remaining variants on whether they are retryable
            _ => true,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ConnectionSide {
    pub(crate) chain: Box<dyn ChainHandle>,
    client_id: ClientId,
    connection_id: ConnectionId,
}

impl ConnectionSide {
    pub fn new(
        chain: Box<dyn ChainHandle>,
        client_id: ClientId,
        connection_id: ConnectionId,
    ) -> Self {
        Self {
            chain,
            client_id,
            connection_id,
        }
    }
}

impl Serialize for ConnectionSide {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        #[derive(Debug, Serialize)]
        struct ConnectionSide<'a> {
            client_id: &'a ClientId,
            connection_id: &'a ConnectionId,
        }

        let value = ConnectionSide {
            client_id: &self.client_id,
            connection_id: &self.connection_id,
        };

        value.serialize(serializer)
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Connection {
    pub delay_period: Duration,
    pub a_side: ConnectionSide,
    pub b_side: ConnectionSide,
}

impl Connection {
    /// Create a new connection, ensuring that the handshake has succeeded and the two connection
    /// ends exist on each side.
    pub fn new(
        a_client: ForeignClient,
        b_client: ForeignClient,
        delay_period: Duration,
    ) -> Result<Self, ConnectionError> {
        Self::validate_clients(&a_client, &b_client)?;

        // Validate the delay period against the upper bound
        if delay_period > MAX_PACKET_DELAY {
            return Err(ConnectionError::ConstructorFailed(format!(
                "Invalid delay period '{:?}': should be max '{:?}'",
                delay_period, MAX_PACKET_DELAY
            )));
        }

        let mut c = Self {
            delay_period,
            a_side: ConnectionSide::new(
                a_client.dst_chain(),
                a_client.id().clone(),
                Default::default(),
            ),
            b_side: ConnectionSide::new(
                b_client.dst_chain(),
                b_client.id().clone(),
                Default::default(),
            ),
        };

        c.handshake()?;

        Ok(c)
    }

    pub fn find(
        a_client: ForeignClient,
        b_client: ForeignClient,
        conn_end_a: &IdentifiedConnectionEnd,
    ) -> Result<Connection, ConnectionError> {
        Self::validate_clients(&a_client, &b_client)?;

        // Validate the connection end
        if conn_end_a.end().client_id().ne(a_client.id()) {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the client id in the connection end ({}) does not match the foreign client id ({})",
                conn_end_a.end().client_id(), a_client.id()
            )));
        }
        if conn_end_a.end().counterparty().client_id() != b_client.id() {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the counterparty client id in the connection end ({}) does not match the foreign client id ({})",
                conn_end_a.end().counterparty().client_id(), b_client.id()
            )));
        }
        if !conn_end_a.end().state_matches(&State::Open) {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the connection end is expected to be in state 'Open'; found state: {:?}",
                conn_end_a.end().state()
            )));
        }
        let b_conn_id = conn_end_a
            .end()
            .counterparty()
            .connection_id()
            .cloned()
            .ok_or_else(|| {
                ConnectionError::ConstructorFailed(format!(
                    "the connection end has no connection id field in the counterparty: {:?}",
                    conn_end_a.end().counterparty()
                ))
            })?;

        let c = Connection {
            delay_period: conn_end_a.end().delay_period(),
            a_side: ConnectionSide {
                chain: a_client.dst_chain.clone(),
                client_id: a_client.id.clone(),
                connection_id: conn_end_a.id().clone(),
            },
            b_side: ConnectionSide {
                chain: b_client.dst_chain.clone(),
                client_id: b_client.id.clone(),
                connection_id: b_conn_id,
            },
        };

        Ok(c)
    }

    // Verifies that the two clients are mutually consistent, i.e., they serve the same two chains.
    fn validate_clients(
        a_client: &ForeignClient,
        b_client: &ForeignClient,
    ) -> Result<(), ConnectionError> {
        if a_client.src_chain().id() != b_client.dst_chain().id() {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the source chain of client a ({}) does not not match the destination chain of client b ({})",
                a_client.src_chain().id(),
                b_client.dst_chain().id()
            )));
        }

        if a_client.dst_chain().id() != b_client.src_chain().id() {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the destination chain of client a ({}) does not not match the source chain of client b ({})",
                a_client.dst_chain().id(),
                b_client.src_chain().id()
            )));
        }

        Ok(())
    }

    pub fn src_chain(&self) -> Box<dyn ChainHandle> {
        self.a_side.chain.clone()
    }

    pub fn dst_chain(&self) -> Box<dyn ChainHandle> {
        self.b_side.chain.clone()
    }

    pub fn src_client_id(&self) -> &ClientId {
        &self.a_side.client_id
    }

    pub fn dst_client_id(&self) -> &ClientId {
        &self.b_side.client_id
    }

    pub fn src_connection_id(&self) -> &ConnectionId {
        &self.a_side.connection_id
    }

    pub fn dst_connection_id(&self) -> &ConnectionId {
        &self.b_side.connection_id
    }

    pub fn flipped(&self) -> Connection {
        Connection {
            a_side: self.b_side.clone(),
            b_side: self.a_side.clone(),
            delay_period: self.delay_period,
        }
    }

    /// Executes a connection handshake protocol (ICS 003) for this connection object
    fn handshake(&mut self) -> Result<(), ConnectionError> {
        let done = '🥂';

        let a_chain = self.a_side.chain.clone();
        let b_chain = self.b_side.chain.clone();

        // Try connOpenInit on a_chain
        let mut counter = 0;
        while counter < MAX_RETRIES {
            counter += 1;
            match self.flipped().build_conn_init_and_send() {
                Err(e) => {
                    error!("Failed ConnInit {:?}: {}", self.a_side, e);
                    continue;
                }
                Ok(result) => {
                    self.a_side.connection_id = extract_connection_id(&result)?.clone();
                    println!("🥂  {} => {:#?}\n", self.a_side.chain.id(), result);
                    break;
                }
            }
        }

        // Try connOpenTry on b_chain
        counter = 0;
        while counter < MAX_RETRIES {
            counter += 1;
            match self.build_conn_try_and_send() {
                Err(e) => {
                    error!("Failed ConnTry {:?}: {}", self.b_side, e);
                    continue;
                }
                Ok(result) => {
                    self.b_side.connection_id = extract_connection_id(&result)?.clone();
                    println!("{}  {} => {:#?}\n", done, self.b_side.chain.id(), result);
                    break;
                }
            }
        }

        counter = 0;
        while counter < MAX_RETRIES {
            counter += 1;

            // Continue loop if query error
            let a_connection = a_chain.query_connection(&self.src_connection_id(), Height::zero());
            if a_connection.is_err() {
                continue;
            }
            let b_connection = b_chain.query_connection(&self.dst_connection_id(), Height::zero());
            if b_connection.is_err() {
                continue;
            }

            match (
                a_connection.unwrap().state().clone(),
                b_connection.unwrap().state().clone(),
            ) {
                (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                    // Ack to a_chain
                    match self.flipped().build_conn_ack_and_send() {
                        Err(e) => error!("Failed ConnAck {:?}: {}", self.a_side, e),
                        Ok(event) => {
                            println!("{}  {} => {:#?}\n", done, self.a_side.chain.id(), event)
                        }
                    }
                }
                (State::Open, State::TryOpen) => {
                    // Confirm to b_chain
                    match self.build_conn_confirm_and_send() {
                        Err(e) => error!("Failed ConnConfirm {:?}: {}", self.b_side, e),
                        Ok(event) => {
                            println!("{}  {} => {:#?}\n", done, self.b_side.chain.id(), event)
                        }
                    }
                }
                (State::TryOpen, State::Open) => {
                    // Confirm to a_chain
                    match self.flipped().build_conn_confirm_and_send() {
                        Err(e) => error!("Failed ConnConfirm {:?}: {}", self.a_side, e),
                        Ok(event) => {
                            println!("{}  {} => {:#?}\n", done, self.a_side.chain.id(), event)
                        }
                    }
                }
                (State::Open, State::Open) => {
                    println!(
                        "{0}{0}{0}  Connection handshake finished for [{1:#?}]\n",
                        done, self
                    );
                    return Ok(());
                }
                _ => {}
            }
        }

        Err(ConnectionError::Failed(format!(
            "Failed to finish connection handshake in {:?} iterations",
            MAX_RETRIES
        )))
    }

    /// Retrieves the connection from destination and compares against the expected connection
    /// built from the message type (`msg_type`) and options (`opts`).
    /// If the expected and the destination connections are compatible, it returns the expected connection
    fn validated_expected_connection(
        &self,
        msg_type: ConnectionMsgType,
    ) -> Result<ConnectionEnd, ConnectionError> {
        let prefix = self
            .src_chain()
            .query_commitment_prefix()
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        // If there is a connection present on the destination chain, it should look like this:
        let counterparty = Counterparty::new(
            self.src_client_id().clone(),
            Option::from(self.src_connection_id().clone()),
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
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        let dst_expected_connection = ConnectionEnd::new(
            highest_state,
            self.dst_client_id().clone(),
            counterparty,
            versions,
            ZERO_DURATION,
        );

        // Retrieve existing connection if any
        let dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::zero())
            .map_err(|e| ConnectionError::QueryError(self.dst_chain().id(), e))?;

        // Check if a connection is expected to exist on destination chain
        // A connection must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dst_connection.state_matches(&State::Uninitialized) {
            return Err(ConnectionError::Failed(format!(
                "missing connection {} on source chain {}",
                self.src_connection_id().clone(),
                self.dst_chain().id()
            )));
        }

        check_destination_connection_state(
            self.dst_connection_id().clone(),
            dst_connection,
            dst_expected_connection.clone(),
        )?;

        Ok(dst_expected_connection)
    }

    pub fn build_update_client_on_src(&self, height: Height) -> Result<Vec<Any>, ConnectionError> {
        let client = self.restore_src_client();
        client.build_update_client(height).map_err(|e| {
            ConnectionError::ClientOperation(self.src_client_id().clone(), self.src_chain().id(), e)
        })
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, ConnectionError> {
        let client = self.restore_dst_client();
        client.build_update_client(height).map_err(|e| {
            ConnectionError::ClientOperation(self.dst_client_id().clone(), self.dst_chain().id(), e)
        })
    }

    pub fn build_conn_init(&self) -> Result<Vec<Any>, ConnectionError> {
        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ConnectionError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        let prefix = self
            .src_chain()
            .query_commitment_prefix()
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        let counterparty = Counterparty::new(self.src_client_id().clone(), None, prefix);

        let version = self
            .dst_chain()
            .query_compatible_versions()
            .map_err(|e| ConnectionError::QueryError(self.dst_chain().id(), e))?[0]
            .clone();

        // Build the domain type message
        let new_msg = MsgConnectionOpenInit {
            client_id: self.dst_client_id().clone(),
            counterparty,
            version,
            delay_period: self.delay_period,
            signer,
        };

        Ok(vec![new_msg.to_any()])
    }

    pub fn build_conn_init_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let dst_msgs = self.build_conn_init()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection init
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenInitConnection(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn init event was in the response".to_string())
            })?;

        // TODO - make chainError an actual error
        match result {
            IbcEvent::OpenInitConnection(_) => Ok(result),
            IbcEvent::ChainError(e) => Err(ConnectionError::Failed(format!(
                "tx response event consists of an error: {}",
                e
            ))),
            _ => panic!("internal error"),
        }
    }

    /// Attempts to build a MsgConnOpenTry.
    pub fn build_conn_try(&self) -> Result<Vec<Any>, ConnectionError> {
        let src_connection = self
            .src_chain()
            .query_connection(self.src_connection_id(), Height::zero())
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

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
            .map_err(|e| ConnectionError::QueryError(self.dst_chain().id(), e))?;
        let client_msgs = self.build_update_client_on_src(src_client_target_height)?;
        self.src_chain()
            .send_msgs(client_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.src_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;
        let (client_state, proofs) = self
            .src_chain()
            .build_connection_proofs_and_client_state(
                ConnectionMsgType::OpenTry,
                self.src_connection_id(),
                self.src_client_id(),
                query_height,
            )
            .map_err(|e| {
                ConnectionError::Failed(format!("failed to build connection proofs: {}", e))
            })?;

        // Build message(s) for updating client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        let counterparty_versions = if src_connection.versions().is_empty() {
            self.src_chain()
                .query_compatible_versions()
                .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?
        } else {
            src_connection.versions()
        };

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ConnectionError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        let prefix = self
            .src_chain()
            .query_commitment_prefix()
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        let counterparty = Counterparty::new(
            self.src_client_id().clone(),
            Option::from(self.src_connection_id().clone()),
            prefix,
        );

        let new_msg = MsgConnectionOpenTry {
            client_id: self.dst_client_id().clone(),
            client_state,
            previous_connection_id: None,
            counterparty,
            counterparty_versions,
            proofs,
            delay_period: delay,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_conn_try_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let dst_msgs = self.build_conn_try()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection try transaction
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenTryConnection(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn try event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenTryConnection(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ConnectionError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }

    /// Attempts to build a MsgConnOpenAck.
    pub fn build_conn_ack(&self) -> Result<Vec<Any>, ConnectionError> {
        let _expected_dst_connection = self
            .validated_expected_connection(ConnectionMsgType::OpenAck)
            .map_err(|e|
                ConnectionError::Failed(format!(
                    "ack options inconsistent with existing connection on destination chain; context={}", e
                )))?;

        let src_connection = self
            .src_chain()
            .query_connection(self.src_connection_id(), Height::zero())
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        // TODO - check that the src connection is consistent with the ack options

        // Build add **send** the message(s) for updating client on source.
        // TODO - add check if it is required
        let src_client_target_height = self
            .dst_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::QueryError(self.dst_chain().id(), e))?;
        let client_msgs = self.build_update_client_on_src(src_client_target_height)?;
        self.src_chain()
            .send_msgs(client_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.src_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;
        let (client_state, proofs) = self
            .src_chain()
            .build_connection_proofs_and_client_state(
                ConnectionMsgType::OpenAck,
                self.src_connection_id(),
                self.src_client_id(),
                query_height,
            )
            .map_err(|e| {
                ConnectionError::Failed(format!("failed to build connection proofs: {}", e))
            })?;

        // Build message(s) for updating client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ConnectionError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        let new_msg = MsgConnectionOpenAck {
            connection_id: self.dst_connection_id().clone(),
            counterparty_connection_id: self.src_connection_id().clone(),
            client_state,
            proofs,
            version: src_connection.versions()[0].clone(),
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_conn_ack_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let dst_msgs = self.build_conn_ack()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection ack
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenAckConnection(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn ack event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenAckConnection(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ConnectionError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }

    /// Attempts to build a MsgConnOpenConfirm.
    pub fn build_conn_confirm(&self) -> Result<Vec<Any>, ConnectionError> {
        let _expected_dst_connection = self
            .validated_expected_connection(ConnectionMsgType::OpenAck)
            .map_err(|e| {
                    ConnectionError::Failed(format!(
                    "confirm options inconsistent with existing connection on destination chain; context={}", e))
            })?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        let _src_connection = self
            .src_chain()
            .query_connection(self.src_connection_id(), query_height)
            .map_err(|_| {
                ConnectionError::Failed(format!(
                    "missing connection {} on source chain",
                    self.src_connection_id()
                ))
            })?;

        // TODO - check that the src connection is consistent with the confirm options

        let (_, proofs) = self
            .src_chain()
            .build_connection_proofs_and_client_state(
                ConnectionMsgType::OpenConfirm,
                self.src_connection_id(),
                self.src_client_id(),
                query_height,
            )
            .map_err(|e| {
                ConnectionError::Failed(format!("failed to build connection proofs: {}", e))
            })?;

        // Build message(s) for updating client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ConnectionError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        let new_msg = MsgConnectionOpenConfirm {
            connection_id: self.dst_connection_id().clone(),
            proofs,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_conn_confirm_and_send(&self) -> Result<IbcEvent, ConnectionError> {
        let dst_msgs = self.build_conn_confirm()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection confirm
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenConfirmConnection(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn confirm event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenConfirmConnection(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ConnectionError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
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

fn extract_connection_id(event: &IbcEvent) -> Result<&ConnectionId, ConnectionError> {
    match event {
        IbcEvent::OpenInitConnection(ev) => ev.connection_id().as_ref(),
        IbcEvent::OpenTryConnection(ev) => ev.connection_id().as_ref(),
        IbcEvent::OpenAckConnection(ev) => ev.connection_id().as_ref(),
        IbcEvent::OpenConfirmConnection(ev) => ev.connection_id().as_ref(),
        _ => None,
    }
    .ok_or_else(|| ConnectionError::Failed("cannot extract connection_id from result".to_string()))
}

/// Enumeration of proof carrying ICS3 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConnectionMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
}

fn check_destination_connection_state(
    connection_id: ConnectionId,
    existing_connection: ConnectionEnd,
    expected_connection: ConnectionEnd,
) -> Result<(), ConnectionError> {
    let good_client_ids = existing_connection.client_id() == expected_connection.client_id()
        && existing_connection.counterparty().client_id()
            == expected_connection.counterparty().client_id();

    let good_state =
        existing_connection.state().clone() as u32 <= expected_connection.state().clone() as u32;

    let good_connection_ids = existing_connection.counterparty().connection_id().is_none()
        || existing_connection.counterparty().connection_id()
            == expected_connection.counterparty().connection_id();

    // TODO check versions and store prefix

    if good_state && good_client_ids && good_connection_ids {
        Ok(())
    } else {
        Err(ConnectionError::Failed(format!(
            "connection {} already exist in an incompatible state",
            connection_id
        )))
    }
}
