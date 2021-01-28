use prost_types::Any;
use thiserror::Error;
use tracing::error;

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

use ibc::events::IBCEvent;
use ibc::ics02_client::height::Height;
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use ibc::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;

use crate::chain::handle::ChainHandle;
use crate::error::Error;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::relay::MAX_ITER;

#[derive(Debug, Error)]
pub enum ConnectionError {
    #[error("failed with underlying cause: {0}")]
    Failed(String),

    #[error("constructor parameters do not match: underlying error: {0}")]
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
    ) -> ConnectionSide {
        Self {
            chain,
            client_id,
            connection_id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Connection {
    pub a_side: ConnectionSide,
    pub b_side: ConnectionSide,
}

impl Connection {
    /// Create a new connection, ensuring that the handshake has succeeded and the two connection
    /// ends exist on each side.
    pub fn new(
        a_client: ForeignClient,
        b_client: ForeignClient,
    ) -> Result<Connection, ConnectionError> {
        // Validate that the two clients serve the same two chains
        if a_client.src_chain().id().ne(&b_client.dst_chain().id()) {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the source chain of client a ({}) does not not match the destination chain of client b ({})",
                a_client.src_chain().id(),
                b_client.dst_chain().id()
            )));
        }
        if a_client.dst_chain().id().ne(&b_client.src_chain().id()) {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the destination chain of client a ({}) does not not match the source chain of client b ({})",
                a_client.dst_chain().id(),
                b_client.src_chain().id()
            )));
        }

        let mut c = Connection {
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
        }
    }

    /// Executes a connection handshake protocol (ICS 003) for this connection object
    fn handshake(&mut self) -> Result<(), ConnectionError> {
        let done = '\u{1F942}'; // surprise emoji

        let a_chain = self.a_side.chain.clone();
        let b_chain = self.b_side.chain.clone();

        // Try connOpenInit on a_chain
        let mut counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match self.flipped().build_conn_init_and_send() {
                Err(e) => {
                    error!("Failed ConnInit {:?}: {}", self.a_side, e);
                    continue;
                }
                Ok(result) => {
                    self.a_side.connection_id = extract_connection_id(&result)?.clone();
                    println!("{}  {} => {:?}\n", done, self.a_side.chain.id(), result);
                    break;
                }
            }
        }

        // Try connOpenTry on b_chain
        counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match self.build_conn_try_and_send() {
                Err(e) => {
                    error!("Failed ConnTry {:?}: {}", self.b_side, e);
                    continue;
                }
                Ok(result) => {
                    self.b_side.connection_id = extract_connection_id(&result)?.clone();
                    println!("{}  {} => {:?}\n", done, self.b_side.chain.id(), result);
                    break;
                }
            }
        }

        counter = 0;
        while counter < MAX_ITER {
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
                        Err(e) => {
                            error!("Failed ConnAck {:?}: {}", self.a_side, e);
                        }
                        Ok(event) => {
                            println!("{}  {} => {:?}\n", done, self.a_side.chain.id(), event)
                        }
                    }
                }
                (State::Open, State::TryOpen) => {
                    // Confirm to b_chain
                    match self.build_conn_confirm_and_send() {
                        Err(e) => error!("Failed ConnConfirm {:?}: {}", self.b_side, e),
                        Ok(event) => {
                            println!("{}  {} => {:?}\n", done, self.b_side.chain.id(), event)
                        }
                    }
                }
                (State::TryOpen, State::Open) => {
                    // Confirm to a_chain
                    match self.flipped().build_conn_confirm_and_send() {
                        Err(e) => error!("Failed ConnConfirm {:?}: {}", self.a_side, e),
                        Ok(event) => {
                            println!("{}  {} => {:?}\n", done, self.a_side.chain.id(), event)
                        }
                    }
                }
                (State::Open, State::Open) => {
                    println!(
                        "{}  {}  {}  Connection handshake finished for [{:#?}]\n",
                        done, done, done, self
                    );
                    return Ok(());
                }
                _ => {}
            }
        }

        Err(ConnectionError::Failed(format!(
            "Failed to finish connection handshake in {:?} iterations",
            MAX_ITER
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
            0,
        );

        // Retrieve existing connection if any
        let dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), ICSHeight::default())
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
        let client = ForeignClient {
            id: self.src_client_id().clone(),
            dst_chain: self.src_chain(),
            src_chain: self.dst_chain(),
        };

        client.build_update_client(height).map_err(|e| {
            ConnectionError::ClientOperation(self.src_client_id().clone(), self.src_chain().id(), e)
        })
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, ConnectionError> {
        let client = ForeignClient {
            id: self.dst_client_id().clone(),
            dst_chain: self.dst_chain(),
            src_chain: self.src_chain(),
        };

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
            delay_period: 0,
            signer,
        };

        Ok(vec![new_msg.to_any::<RawMsgConnectionOpenInit>()])
    }

    pub fn build_conn_init_and_send(&self) -> Result<IBCEvent, ConnectionError> {
        let dst_msgs = self.build_conn_init()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection init
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenInitConnection(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn init event was in the response".to_string())
            })?;

        // TODO - make chainError an actual error
        match result {
            IBCEvent::OpenInitConnection(_) => Ok(result),
            IBCEvent::ChainError(e) => Err(ConnectionError::Failed(format!(
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
            .query_connection(self.src_connection_id(), ICSHeight::default())
            .map_err(|e| ConnectionError::QueryError(self.src_chain().id(), e))?;

        // TODO - check that the src connection is consistent with the try options

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
            delay_period: 0,
            signer,
        };

        let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenTry>()];

        msgs.append(&mut new_msgs);

        Ok(msgs)
    }

    pub fn build_conn_try_and_send(&self) -> Result<IBCEvent, ConnectionError> {
        let dst_msgs = self.build_conn_try()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection try transaction
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenTryConnection(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn try event was in the response".to_string())
            })?;

        match result {
            IBCEvent::OpenTryConnection(_) => Ok(result),
            IBCEvent::ChainError(e) => {
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
            .query_connection(self.src_connection_id(), ICSHeight::default())
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
            counterparty_connection_id: Option::from(self.src_connection_id().clone()),
            client_state,
            proofs,
            version: src_connection.versions()[0].clone(),
            signer,
        };

        let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenAck>()];

        msgs.append(&mut new_msgs);

        Ok(msgs)
    }

    pub fn build_conn_ack_and_send(&self) -> Result<IBCEvent, ConnectionError> {
        let dst_msgs = self.build_conn_ack()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection ack
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenAckConnection(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn ack event was in the response".to_string())
            })?;

        match result {
            IBCEvent::OpenAckConnection(_) => Ok(result),
            IBCEvent::ChainError(e) => {
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

        let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenConfirm>()];

        msgs.append(&mut new_msgs);

        Ok(msgs)
    }

    pub fn build_conn_confirm_and_send(&self) -> Result<IBCEvent, ConnectionError> {
        let dst_msgs = self.build_conn_confirm()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ConnectionError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for connection confirm
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenConfirmConnection(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ConnectionError::Failed("no conn confirm event was in the response".to_string())
            })?;

        match result {
            IBCEvent::OpenConfirmConnection(_) => Ok(result),
            IBCEvent::ChainError(e) => {
                Err(ConnectionError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }
}

fn extract_connection_id(event: &IBCEvent) -> Result<&ConnectionId, ConnectionError> {
    match event {
        IBCEvent::OpenInitConnection(ev) => ev.connection_id().as_ref(),
        IBCEvent::OpenTryConnection(ev) => ev.connection_id().as_ref(),
        IBCEvent::OpenAckConnection(ev) => ev.connection_id().as_ref(),
        IBCEvent::OpenConfirmConnection(ev) => ev.connection_id().as_ref(),
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
