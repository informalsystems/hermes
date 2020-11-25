use prost_types::Any;
use std::str::FromStr;
use std::time::SystemTime;
use thiserror::Error;

use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

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
use crate::error::{Error, Kind};
use crate::foreign_client::{build_update_client, ForeignClient};
use crate::config;

#[derive(Debug, Error)]
pub enum ConnectionError {
    #[error("Failed")]
    Failed(String),
}

#[derive(Clone, Debug)]
pub struct Connection {
    pub config: ConnectionConfig,
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
    pub src_config: ConnectionSideConfig,
    pub dst_config: ConnectionSideConfig,
}

impl ConnectionConfig {
    pub fn new(conn: &config::Connection) -> Result<ConnectionConfig, String> {

        let src_conn_endpoint = conn.src.clone()
            .ok_or("Connection source endpoint not specified")?;
        let dst_conn_endpoint = conn.dest.clone()
            .ok_or("Connection destination endpoint not specified")?;


        let src_config = ConnectionSideConfig {
            chain_id: ChainId::from_str(src_conn_endpoint
                .chain_id.as_str())
                .map_err(|e| format!("Invalid chain id ({:?})", e))?,
            connection_id: ConnectionId::from_str(src_conn_endpoint
                .connection_id
                .ok_or("Connection id not specified")?
                .as_str())
                .map_err(|e| format!("Invalid connection id ({:?})", e))?,
            client_id: ClientId::from_str(src_conn_endpoint
                .client_id.as_str())
                .map_err(|e| format!("Invalid client id ({:?})", e))?,
        };

        let dst_config = ConnectionSideConfig {
            chain_id: ChainId::from_str(dst_conn_endpoint
                .chain_id.as_str())
                .map_err(|e| format!("Invalid counterparty chain id ({:?})", e))?,
            connection_id: ConnectionId::from_str(dst_conn_endpoint
                .connection_id
                .ok_or("Counterparty connection id not specified")?
                .as_str())
                .map_err(|e| format!("Invalid counterparty connection id ({:?})", e))?,
            client_id: ClientId::from_str(dst_conn_endpoint
                .client_id.as_str())
                .map_err(|e| format!("Invalid counterparty client id ({:?})", e))?,
        };

        Ok(ConnectionConfig {
            src_config,
            dst_config,
        })
    }
}

// TODO - in the loop below calling build_conn_*_and_send() directly doesn't work, investigate why
// For this reason at this point we first call build_conn_*() to get the messages and then
// we send them.
impl Connection {
    pub fn new(
        src_chain: impl ChainHandle,
        dst_chain: impl ChainHandle,
        _src_client: ForeignClient,
        _dst_client: ForeignClient,
        config: ConnectionConfig,
    ) -> Result<Connection, ConnectionError> {
        let done = '\u{1F378}'; // surprise emoji

        let flipped = ConnectionConfig {
            src_config: config.dst_config.clone(),
            dst_config: config.src_config.clone(),
        };

        let mut counter = 0;
        while counter < 10 {
            counter += 1;
            let now = SystemTime::now();

            let src_connection = src_chain
                .query_connection(&config.src_config.connection_id.clone(), Height::default());
            let dst_connection = dst_chain
                .query_connection(&config.dst_config.connection_id.clone(), Height::default());

            match (src_connection, dst_connection) {
                (Err(_), Err(_)) => {
                    // Init to src
                    match build_conn_init(src_chain.clone(), dst_chain.clone(), &flipped) {
                        Err(e) => println!("{:?} Failed ConnInit {:?}", e, flipped.dst_config),
                        Ok(src_msgs) => {
                            src_chain.send_tx(src_msgs).unwrap();
                            println!("{} ConnInit {:?}", done, flipped.dst_config);
                        }
                    }
                }
                (Ok(src_connection), Err(_)) => {
                    assert!(src_connection.state_matches(&State::Init));
                    match build_conn_try(dst_chain.clone(), src_chain.clone(), &config) {
                        Err(e) => println!("{:?} Failed ConnTry {:?}", e, config.dst_config),
                        Ok(dst_msgs) => {
                            dst_chain.send_tx(dst_msgs).unwrap();
                            println!("{} ConnTry {:?}", done, config.dst_config);
                        }
                    }
                }
                (Err(_), Ok(dst_connection)) => {
                    assert!(dst_connection.state_matches(&State::Init));
                    match build_conn_try(src_chain.clone(), dst_chain.clone(), &flipped) {
                        Err(e) => {
                            println!("{:?} Failed ConnTry {:?}", e, flipped)
                        }
                        Ok(src_msgs) => {
                            src_chain.send_tx(src_msgs).unwrap();
                            println!("{} ConnTry {:?}", done, flipped);
                        }
                    }
                }
                (Ok(src_connection), Ok(dst_connection)) => {
                    match (src_connection.state(), dst_connection.state()) {
                        (&State::Init, &State::Init) => {
                            // Try to dest
                            match build_conn_try(dst_chain.clone(), src_chain.clone(), &config) {
                                Err(e) => println!("{:?} Failed ConnTry {:?}", e, config.dst_config),
                                Ok(dst_msgs) => {
                                    dst_chain.send_tx(dst_msgs).unwrap();
                                    println!("{} ConnTry {:?}", done, config.dst_config);
                                }
                            }
                        }
                        (&State::TryOpen, &State::Init) => {
                            // Ack to dest
                            match build_conn_ack(dst_chain.clone(), src_chain.clone(), &config) {
                                Err(e) => println!("{:?} Failed ConnAck {:?}", e, config),
                                Ok(dst_msgs) => {
                                    dst_chain.send_tx(dst_msgs).unwrap();
                                    println!("{} ConnAck {:?}", done, config);
                                }
                            }
                        }
                        (&State::Init, &State::TryOpen) | (&State::TryOpen, &State::TryOpen) => {
                            // Ack to src
                            match build_conn_ack(src_chain.clone(), dst_chain.clone(), &flipped) {
                                Err(e) => println!("{:?} Failed ConnAck {:?}", e, flipped),
                                Ok(src_msgs) => {
                                    src_chain.send_tx(src_msgs).unwrap();
                                    println!("{} ConnAck {:?}", done, flipped);
                                }
                            }
                        }
                        (&State::Open, &State::TryOpen) => {
                            // Confirm to dest
                            match build_conn_confirm(dst_chain.clone(), src_chain.clone(), &config) {
                                Err(e) => println!("{:?} Failed ConnConfirm {:?}", e, config),
                                Ok(dst_msgs) => {
                                    dst_chain.send_tx(dst_msgs).unwrap();
                                    println!("{} ConnConfirm {:?}", done, config);
                                }
                            }
                        }
                        (&State::TryOpen, &State::Open) => {
                            // Confirm to src
                            match build_conn_confirm(src_chain.clone(), dst_chain.clone(), &flipped) {
                                Err(e) => println!("{:?} ConnConfirm {:?}", e, flipped),
                                Ok(src_msgs) => {
                                    src_chain.send_tx(src_msgs).unwrap();
                                    println!("{} ConnConfirm {:?}", done, flipped);
                                }
                            }
                        }
                        (&State::Open, &State::Open) => {
                            println!(
                                "{} {} {} ====> Connection handshake finished for [{:#?}]",
                                done, done, done, config
                            );
                            break;
                        }
                        _ => {}
                    }
                }
            }
            println!("elapsed time {:?}\n", now.elapsed().unwrap().as_secs());
        }

        Ok(Connection { config })
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
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ConnectionConfig,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the connection
    if dst_chain
        .query_connection(&opts.dst_config.connection_id(), ICSHeight::default())
        .is_ok()
    {
        return Err(Kind::ConnOpenInit(
            opts.dst_config.connection_id().clone(),
            "connection already exist".into(),
        )
        .into());
    }

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let prefix = src_chain.query_commitment_prefix()?;

    let counterparty = Counterparty::new(
        opts.src_config.client_id().clone(),
        Some(opts.src_config.connection_id().clone()),
        prefix,
    );

    // Build the domain type message
    let new_msg = MsgConnectionOpenInit {
        client_id: opts.dst_config.client_id().clone(),
        connection_id: opts.dst_config.connection_id().clone(),
        counterparty,
        version: dst_chain.query_compatible_versions()?[0].clone(),
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgConnectionOpenInit>()])
}

pub fn build_conn_init_and_send(
    src_chain: impl ChainHandle,
    dst_chain: impl ChainHandle,
    opts: &ConnectionConfig,
) -> Result<String, Error> {
    let dst_msgs = build_conn_init(dst_chain.clone(), src_chain, opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
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
        Err(Kind::ConnOpenTry(
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
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    msg_type: ConnectionMsgType,
    opts: &ConnectionConfig,
) -> Result<ConnectionEnd, Error> {
    // If there is a connection present on the destination chain, it should look like this:
    let counterparty = Counterparty::new(
        opts.src_config.client_id().clone(),
        Option::from(opts.src_config.connection_id().clone()),
        src_chain.query_commitment_prefix()?,
    );

    // The highest expected state, depends on the message type:
    let highest_state = match msg_type {
        ConnectionMsgType::OpenTry => State::Init,
        ConnectionMsgType::OpenAck => State::TryOpen,
        ConnectionMsgType::OpenConfirm => State::TryOpen,
    };

    let dst_expected_connection = ConnectionEnd::new(
        highest_state,
        opts.dst_config.client_id().clone(),
        counterparty,
        src_chain.query_compatible_versions()?,
    )
    .unwrap();

    // Retrieve existing connection if any
    let dst_connection = dst_chain.query_connection(
        &opts.dst_config.connection_id().clone(),
        ICSHeight::default(),
    );

    // Check if a connection is expected to exist on destination chain
    if msg_type == ConnectionMsgType::OpenTry {
        // TODO - check typed Err, or make query_connection return Option<ConnectionEnd>
        // It is ok if there is no connection for Try Tx
        if dst_connection.is_err() {
            return Ok(dst_expected_connection);
        }
    } else {
        // A connection must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dst_connection.is_err() {
            return Err(Kind::ConnOpenTry(
                opts.src_config.connection_id().clone(),
                "missing connection on source chain".to_string(),
            )
            .into());
        }
    }

    check_destination_connection_state(
        opts.dst_config.connection_id().clone(),
        dst_connection?,
        dst_expected_connection.clone(),
    )?;

    Ok(dst_expected_connection)
}

/// Attempts to build a MsgConnOpenTry.
pub fn build_conn_try(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ConnectionConfig,
) -> Result<Vec<Any>, Error> {
    let dst_expected_connection = validated_expected_connection(
        dst_chain.clone(),
        src_chain.clone(),
        ConnectionMsgType::OpenTry,
        opts,
    )
    .map_err(|e| {
        Kind::ConnOpenTry(
            opts.src_config.connection_id().clone(),
            "try options inconsistent with existing connection on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_connection = src_chain
        .query_connection(
            &opts.src_config.connection_id().clone(),
            ICSHeight::default(),
        )
        .map_err(|e| {
            Kind::ConnOpenTry(
                opts.src_config.connection_id().clone(),
                "missing connection on source chain".to_string(),
            )
            .context(e)
        })?;

    // TODO - check that the src connection is consistent with the try options

    // Build add send the message(s) for updating client on source
    // TODO - add check if it is required
    let src_client_target_height = dst_chain.query_latest_height()?;
    let client_msgs = build_update_client(
        src_chain.clone(),
        dst_chain.clone(),
        &opts.src_config.client_id(),
        src_client_target_height,
    )?;
    src_chain.send_tx(client_msgs)?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst_config.client_id(),
        ics_target_height,
    )?;

    let (client_state, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenTry,
        &opts.src_config.connection_id().clone(),
        &opts.src_config.client_id(),
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

    let new_msg = MsgConnectionOpenTry {
        connection_id: opts.dst_config.connection_id().clone(),
        client_id: opts.dst_config.client_id().clone(),
        client_state,
        counterparty_chosen_connection_id: src_connection.counterparty().connection_id().cloned(),
        counterparty: dst_expected_connection.counterparty(),
        counterparty_versions,
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenTry>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_try_and_send(
    src_chain: impl ChainHandle,
    dst_chain: impl ChainHandle,
    opts: &ConnectionConfig,
) -> Result<String, Error> {
    let dst_msgs = build_conn_try(dst_chain.clone(), src_chain, &opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
}

/// Attempts to build a MsgConnOpenAck.
pub fn build_conn_ack(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
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
            opts.dst_config.connection_id().clone(),
            "ack options inconsistent with existing connection on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_connection = src_chain
        .query_connection(
            &opts.src_config.connection_id().clone(),
            ICSHeight::default(),
        )
        .map_err(|e| {
            Kind::ConnOpenAck(
                opts.src_config.connection_id().clone(),
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
        &opts.src_config.client_id(),
        src_client_target_height,
    )?;
    src_chain.send_tx(client_msgs)?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &opts.dst_config.client_id(),
        ics_target_height,
    )?;

    let (client_state, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenAck,
        &opts.src_config.connection_id().clone(),
        &opts.src_config.client_id(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let new_msg = MsgConnectionOpenAck {
        connection_id: opts.dst_config.connection_id().clone(),
        counterparty_connection_id: Option::from(opts.src_config.connection_id().clone()),
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
    src_chain: impl ChainHandle,
    dst_chain: impl ChainHandle,
    opts: &ConnectionConfig,
) -> Result<String, Error> {
    let dst_msgs = build_conn_ack(dst_chain.clone(), src_chain, opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
}

/// Attempts to build a MsgConnOpenConfirm.
pub fn build_conn_confirm(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
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
            opts.src_config.connection_id().clone(),
            "confirm options inconsistent with existing connection on destination chain"
                .to_string(),
        )
        .context(e)
    })?;

    let _src_connection = src_chain
        .query_connection(
            &opts.src_config.connection_id().clone(),
            ICSHeight::default(),
        )
        .map_err(|e| {
            Kind::ConnOpenAck(
                opts.src_config.connection_id().clone(),
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
        &opts.dst_config.client_id(),
        ics_target_height,
    )?;

    let (_, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenConfirm,
        &opts.src_config.connection_id().clone(),
        &opts.src_config.client_id(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let new_msg = MsgConnectionOpenConfirm {
        connection_id: opts.dst_config.connection_id().clone(),
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenConfirm>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_confirm_and_send(
    src_chain: impl ChainHandle,
    dst_chain: impl ChainHandle,
    opts: &ConnectionConfig,
) -> Result<String, Error> {
    let dst_msgs = build_conn_confirm(dst_chain.clone(), src_chain, &opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
}
