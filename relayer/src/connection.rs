use prost_types::Any;
use std::str::FromStr;
use std::time::SystemTime;
use thiserror::Error;
use tracing::{debug, error, info};

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
use crate::config;
use crate::error::{Error, Kind};
use crate::foreign_client::{build_update_client, ForeignClient};
use crate::relay::MAX_ITER;

#[derive(Debug, Error)]
pub enum ConnectionError {
    #[error("Failed")]
    Failed(String),

    #[error("constructor parameters do not match")]
    ConstructorFailed(String),
}

#[derive(Clone, Debug)]
pub struct Connection {
    config: ConnectionConfig,
    a_client: ForeignClient,
    b_client: ForeignClient,
}

#[derive(Clone, Debug)]
pub struct ConnectionSideConfig {
    chain_id: ChainId,
    connection_id: ConnectionId,
    client_id: ClientId,
}

impl ConnectionSideConfig {
    pub fn new(
        chain_id: ChainId,
        connection_id: ConnectionId,
        client_id: ClientId,
    ) -> ConnectionSideConfig {
        Self {
            chain_id,
            connection_id,
            client_id,
        }
    }

    pub fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }

    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }
}

#[derive(Clone, Debug)]
pub struct ConnectionConfig {
    pub a_config: ConnectionSideConfig,
    pub b_config: ConnectionSideConfig,
}

impl ConnectionConfig {
    pub fn src(&self) -> &ConnectionSideConfig {
        &self.a_config
    }

    pub fn dst(&self) -> &ConnectionSideConfig {
        &self.b_config
    }

    pub fn a_end(&self) -> &ConnectionSideConfig {
        &self.a_config
    }

    pub fn b_end(&self) -> &ConnectionSideConfig {
        &self.b_config
    }

    pub fn flipped(&self) -> ConnectionConfig {
        ConnectionConfig {
            a_config: self.b_config.clone(),
            b_config: self.a_config.clone(),
        }
    }
}

impl ConnectionConfig {
    pub fn new(conn: &config::Connection) -> Result<ConnectionConfig, String> {
        let a_conn_endpoint = conn
            .a_end
            .clone()
            .ok_or("Connection source endpoint not specified")?;
        let b_conn_endpoint = conn
            .b_end
            .clone()
            .ok_or("Connection destination endpoint not specified")?;

        let a_config = ConnectionSideConfig {
            chain_id: ChainId::from_str(a_conn_endpoint.chain_id.as_str())
                .map_err(|e| format!("Invalid chain id ({:?})", e))?,
            connection_id: ConnectionId::from_str(
                a_conn_endpoint
                    .connection_id
                    .ok_or("Connection id not specified")?
                    .as_str(),
            )
            .map_err(|e| format!("Invalid connection id ({:?})", e))?,
            client_id: ClientId::from_str(a_conn_endpoint.client_id.as_str())
                .map_err(|e| format!("Invalid client id ({:?})", e))?,
        };

        let b_config = ConnectionSideConfig {
            chain_id: ChainId::from_str(b_conn_endpoint.chain_id.as_str())
                .map_err(|e| format!("Invalid counterparty chain id ({:?})", e))?,
            connection_id: ConnectionId::from_str(
                b_conn_endpoint
                    .connection_id
                    .ok_or("Counterparty connection id not specified")?
                    .as_str(),
            )
            .map_err(|e| format!("Invalid counterparty connection id ({:?})", e))?,
            client_id: ClientId::from_str(b_conn_endpoint.client_id.as_str())
                .map_err(|e| format!("Invalid counterparty client id ({:?})", e))?,
        };

        Ok(ConnectionConfig { a_config, b_config })
    }
}

impl Connection {
    /// Create a new connection, ensuring that the handshake has succeeded and the two connection
    /// ends exist on each side.
    pub fn new(
        a_client: ForeignClient,
        b_client: ForeignClient,
        config: ConnectionConfig,
    ) -> Result<Connection, ConnectionError> {
        // Validate that the two clients serve the same two chains
        if a_client.src_chain().id().ne(&b_client.dst_chain().id()) {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the source chain of client a ({}) does not not match the destination chain of client b ({})",
                a_client.src_chain().id(),
                b_client.dst_chain().id()
            )));
        } else if a_client.dst_chain().id().ne(&b_client.src_chain().id()) {
            return Err(ConnectionError::ConstructorFailed(format!(
                "the destination chain of client a ({}) does not not match the source chain of client b ({})",
                a_client.dst_chain().id(),
                b_client.src_chain().id()
            )));
        }

        let mut c = Connection {
            config,
            a_client,
            b_client,
        };
        c.handshake()?;

        Ok(c)
    }

    /// Returns the "a" side of the connection.
    pub fn chain_a(&self) -> Box<dyn ChainHandle> {
        self.a_client.dst_chain()
    }

    /// Returns the "b" side of the connection.
    pub fn chain_b(&self) -> Box<dyn ChainHandle> {
        self.b_client.dst_chain()
    }

    /// Executes a connection handshake protocol (ICS 003) for this connection object
    fn handshake(&mut self) -> Result<(), ConnectionError> {
        let done = '\u{1F942}'; // surprise emoji

        let a_chain = self.chain_a();
        let b_chain = self.chain_b();

        let mut flipped = self.config.flipped();

        // Try connOpenInit on a_chain
        let now = SystemTime::now();
        let mut counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match build_conn_init_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                Err(e) => {
                    error!("Failed ConnInit {:?}: {}", self.config.a_end(), e);
                    continue;
                }
                Ok(result) => {
                    self.config.a_config.connection_id = extract_connection_id(&result)?.clone();
                    info!("{}  {} => {:?}\n", done, a_chain.id(), result);
                    break;
                }
            }
        }
        debug!("elapsed time {:?}", now.elapsed().unwrap().as_secs());
        let now = SystemTime::now();

        // Try connOpenTry on b_chain
        counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match build_conn_try_and_send(b_chain.clone(), a_chain.clone(), &self.config) {
                Err(e) => {
                    error!("Failed ConnTry {:?}: {}", self.config.b_end(), e);
                    continue;
                }
                Ok(result) => {
                    self.config.b_config.connection_id = extract_connection_id(&result)?.clone();
                    info!("{}  {} => {:?}\n", done, b_chain.id(), result);
                    break;
                }
            }
        }
        debug!("elapsed time {:?}", now.elapsed().unwrap().as_secs());

        flipped = self.config.flipped();
        counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            let now = SystemTime::now();

            // Continue loop if query error
            let a_connection =
                a_chain.query_connection(&self.config.a_end().connection_id, Height::zero());
            if a_connection.is_err() {
                continue;
            }
            let b_connection =
                b_chain.query_connection(&self.config.b_end().connection_id, Height::zero());
            if b_connection.is_err() {
                continue;
            }

            match (
                a_connection.unwrap().state().clone(),
                b_connection.unwrap().state().clone(),
            ) {
                (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                    // Ack to src
                    match build_conn_ack_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                        Err(e) => {
                            error!("Failed ConnAck {:?}: {}", self.config.a_end(), e);
                        }
                        Ok(event) => info!("{}  {} => {:?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::TryOpen) => {
                    // Confirm to dest
                    match build_conn_confirm_and_send(
                        b_chain.clone(),
                        a_chain.clone(),
                        &self.config,
                    ) {
                        Err(e) => error!("Failed ConnConfirm {:?}: {}", self.config.b_end(), e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, b_chain.id(), event),
                    }
                }
                (State::TryOpen, State::Open) => {
                    // Confirm to src
                    match build_conn_confirm_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                        Err(e) => error!("Failed ConnConfirm {:?}: {}", self.config.a_end(), e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::Open) => {
                    info!(
                        "\n{}  {}  {}  Connection handshake finished for [{:#?}]",
                        done, done, done, self.config
                    );
                    return Ok(());
                }
                _ => {}
            }
            debug!("elapsed time {:?}", now.elapsed().unwrap().as_secs());
        }

        Err(ConnectionError::Failed(format!(
            "Failed to finish connection handshake in {:?} iterations",
            MAX_ITER
        )))
    }
}

fn extract_connection_id(event: &IBCEvent) -> Result<&ConnectionId, ConnectionError> {
    match event {
        IBCEvent::OpenInitConnection(ev) => Ok(ev.connection_id()),
        IBCEvent::OpenTryConnection(ev) => Ok(ev.connection_id()),
        IBCEvent::OpenAckConnection(ev) => Ok(ev.connection_id()),
        IBCEvent::OpenConfirmConnection(ev) => Ok(ev.connection_id()),
        _ => Err(ConnectionError::Failed(
            "cannot extract connection_id from result".to_string(),
        )),
    }
}

/// Enumeration of proof carrying ICS3 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConnectionMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
}

pub fn build_conn_init(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<Vec<Any>, Error> {
    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let prefix = src_chain.query_commitment_prefix()?;

    let counterparty = Counterparty::new(opts.src().client_id().clone(), None, prefix);

    // Build the domain type message
    let new_msg = MsgConnectionOpenInit {
        client_id: opts.dst().client_id().clone(),
        counterparty,
        version: dst_chain.query_compatible_versions()?[0].clone(),
        delay_period: 0,
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgConnectionOpenInit>()])
}

pub fn build_conn_init_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_conn_init(dst_chain.clone(), src_chain, opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for connection init
    let result = events
        .iter()
        .find(|&event| {
            matches!(event, IBCEvent::OpenInitConnection(_))
                || matches!(event, IBCEvent::ChainError(_))
        })
        .cloned()
        .ok_or_else(|| Kind::ConnOpenInit("no conn init event was in the response".to_string()))?;

    match result {
        IBCEvent::OpenInitConnection(_) => Ok(result),
        IBCEvent::ChainError(e) => Err(Kind::ConnOpenInit(e).into()),
        _ => panic!("internal error"),
    }
}

fn check_destination_connection_state(
    connection_id: ConnectionId,
    existing_connection: ConnectionEnd,
    expected_connection: ConnectionEnd,
) -> Result<(), Error> {
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
        Err(Kind::ConnOpen(
            connection_id,
            "connection already exist in an incompatible state".into(),
        )
        .into())
    }
}

/// Retrieves the connection from destination and compares against the expected connection
/// built from the message type (`msg_type`) and options (`opts`).
/// If the expected and the destination connections are compatible, it returns the expected connection
fn validated_expected_connection(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    msg_type: ConnectionMsgType,
    opts: &ConnectionConfig,
) -> Result<ConnectionEnd, Error> {
    // If there is a connection present on the destination chain, it should look like this:
    let counterparty = Counterparty::new(
        opts.src().client_id().clone(),
        Option::from(opts.src().connection_id().clone()),
        src_chain.query_commitment_prefix()?,
    );

    // The highest expected state, depends on the message type:
    let highest_state = match msg_type {
        ConnectionMsgType::OpenAck => State::TryOpen,
        ConnectionMsgType::OpenConfirm => State::TryOpen,
        _ => State::Uninitialized,
    };

    let dst_expected_connection = ConnectionEnd::new(
        highest_state,
        opts.dst().client_id().clone(),
        counterparty,
        src_chain.query_compatible_versions()?,
        0,
    );

    // Retrieve existing connection if any
    let dst_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), ICSHeight::default())?;

    // Check if a connection is expected to exist on destination chain
    // A connection must exist on destination chain for Ack and Confirm Tx-es to succeed
    if dst_connection.state_matches(&State::Uninitialized) {
        return Err(Kind::ConnOpen(
            opts.src().connection_id().clone(),
            "missing connection on source chain".to_string(),
        )
        .into());
    }

    check_destination_connection_state(
        opts.dst().connection_id().clone(),
        dst_connection,
        dst_expected_connection.clone(),
    )?;

    Ok(dst_expected_connection)
}

/// Attempts to build a MsgConnOpenTry.
pub fn build_conn_try(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<Vec<Any>, Error> {
    let src_connection = src_chain
        .query_connection(&opts.src().connection_id().clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenTry("missing connection on source chain".to_string()).context(e)
        })?;

    // TODO - check that the src connection is consistent with the try options

    // Build add send the message(s) for updating client on source
    // TODO - add check if update client is required
    let src_client_target_height = dst_chain.query_latest_height()?;
    let client_msgs = build_update_client(
        src_chain.clone(),
        dst_chain.clone(),
        &opts.src().client_id(),
        src_client_target_height,
    )?;
    src_chain.send_msgs(client_msgs)?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst().client_id(),
        ics_target_height,
    )?;

    let (client_state, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenTry,
        &opts.src().connection_id().clone(),
        &opts.src().client_id(),
        ics_target_height,
    )?;

    let counterparty_versions = if src_connection.versions().is_empty() {
        src_chain.query_compatible_versions()?
    } else {
        src_connection.versions()
    };

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let counterparty = Counterparty::new(
        opts.src().client_id().clone(),
        Option::from(opts.src().connection_id().clone()),
        src_chain.query_commitment_prefix()?,
    );

    let new_msg = MsgConnectionOpenTry {
        client_id: opts.dst().client_id().clone(),
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

pub fn build_conn_try_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_conn_try(dst_chain.clone(), src_chain, &opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for connection try transaction
    events
        .iter()
        .find(|&event| {
            matches!(event, IBCEvent::OpenTryConnection(_))
                || matches!(event, IBCEvent::ChainError(_))
        })
        .cloned()
        .ok_or_else(|| {
            Kind::ConnOpenTry("no conn try event was in the response".to_string()).into()
        })
}

/// Attempts to build a MsgConnOpenAck.
pub fn build_conn_ack(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<Vec<Any>, Error> {
    let _expected_dst_connection = validated_expected_connection(
        dst_chain.clone(),
        src_chain.clone(),
        ConnectionMsgType::OpenAck,
        opts,
    )
    .map_err(|e| {
        Kind::ConnOpenAck(
            opts.dst().connection_id().clone(),
            "ack options inconsistent with existing connection on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_connection = src_chain
        .query_connection(&opts.src().connection_id().clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenAck(
                opts.src().connection_id().clone(),
                "missing connection on source chain".to_string(),
            )
            .context(e)
        })?;

    // TODO - check that the src connection is consistent with the ack options

    // Build add **send** the message(s) for updating client on source.
    // TODO - add check if it is required
    // Build add send the message(s) for updating client on source
    // TODO - add check if it is required
    let src_client_target_height = dst_chain.query_latest_height()?;
    let client_msgs = build_update_client(
        src_chain.clone(),
        dst_chain.clone(),
        &opts.src().client_id(),
        src_client_target_height,
    )?;
    src_chain.send_msgs(client_msgs)?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst().client_id(),
        ics_target_height,
    )?;

    let (client_state, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenAck,
        &opts.src().connection_id().clone(),
        &opts.src().client_id(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let new_msg = MsgConnectionOpenAck {
        connection_id: opts.dst().connection_id().clone(),
        counterparty_connection_id: Option::from(opts.src().connection_id().clone()),
        client_state,
        proofs,
        version: src_connection.versions()[0].clone(),
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenAck>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_ack_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_conn_ack(dst_chain.clone(), src_chain, opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for connection ack
    events
        .iter()
        .find(|&event| {
            matches!(event, IBCEvent::OpenAckConnection(_))
                || matches!(event, IBCEvent::ChainError(_))
        })
        .cloned()
        .ok_or_else(|| {
            Kind::ConnOpenAck(
                opts.dst().connection_id().clone(),
                "no conn ack event was in the response".to_string(),
            )
            .into()
        })
}

/// Attempts to build a MsgConnOpenConfirm.
pub fn build_conn_confirm(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<Vec<Any>, Error> {
    let _expected_dst_connection = validated_expected_connection(
        dst_chain.clone(),
        src_chain.clone(),
        ConnectionMsgType::OpenAck,
        opts,
    )
    .map_err(|e| {
        Kind::ConnOpenConfirm(
            opts.src().connection_id().clone(),
            "confirm options inconsistent with existing connection on destination chain"
                .to_string(),
        )
        .context(e)
    })?;

    let _src_connection = src_chain
        .query_connection(&opts.src().connection_id().clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenAck(
                opts.src().connection_id().clone(),
                "missing connection on source chain".to_string(),
            )
            .context(e)
        })?;

    // TODO - check that the src connection is consistent with the confirm options

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst().client_id(),
        ics_target_height,
    )?;

    let (_, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenConfirm,
        &opts.src().connection_id().clone(),
        &opts.src().client_id(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let new_msg = MsgConnectionOpenConfirm {
        connection_id: opts.dst().connection_id().clone(),
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenConfirm>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_confirm_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ConnectionConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_conn_confirm(dst_chain.clone(), src_chain, &opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for connection confirm
    events
        .iter()
        .find(|&event| {
            matches!(event, IBCEvent::OpenConfirmConnection(_))
                || matches!(event, IBCEvent::ChainError(_))
        })
        .cloned()
        .ok_or_else(|| {
            Kind::ConnOpenConfirm(
                opts.dst().connection_id().clone(),
                "no conn confirm event was in the response".to_string(),
            )
            .into()
        })
}
