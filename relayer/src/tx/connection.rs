use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use std::thread;
use std::time::Duration;

use prost_types::Any;
use serde_json::Value;

use bitcoin::hashes::hex::ToHex;

use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

use ibc::ics02_client::state::ClientState;
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::version::get_compatible_versions;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;

use crate::chain::{handle::ChainHandle, runtime::ChainRuntime, Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};
use crate::light_client::tendermint::LightClient as TMLightClient;
use crate::tx::client::{build_update_client, build_update_client_and_send, ClientOptions};
use ibc::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;

#[derive(Clone, Debug)]
pub struct ConnectionOpenInitOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_client_id: ClientId,
    pub src_client_id: ClientId,
    pub dst_connection_id: ConnectionId,
    pub src_connection_id: Option<ConnectionId>,
    pub signer_seed: String,
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
    opts: &ConnectionOpenInitOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the connection
    if dst_chain
        .query_connection(&opts.dst_connection_id, ICSHeight::default())
        .is_ok()
    {
        return Err(Kind::ConnOpenInit(
            opts.dst_connection_id.clone(),
            "connection already exist".into(),
        )
        .into());
    }

    // Get the signer from key seed file
    let (_, signer) = dst_chain.key_and_signer(opts.signer_seed.clone())?;

    let prefix = src_chain.query_commitment_prefix()?;

    let counterparty = Counterparty::new(
        opts.src_client_id.clone(),
        opts.src_connection_id.clone(),
        prefix,
    );

    // Build the domain type message
    let new_msg = MsgConnectionOpenInit {
        client_id: opts.dst_client_id.clone(),
        connection_id: opts.dst_connection_id.clone(),
        counterparty,
        version: dst_chain.query_compatible_versions()?[0].clone(),
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgConnectionOpenInit>()])
}

pub fn build_conn_init_and_send(opts: &ConnectionOpenInitOptions) -> Result<String, Error> {
    // Initialize the source and destination runtimes and light clients
    let (src_chain, _) = ChainRuntime::spawn(opts.src_chain_config.clone())?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.dst_chain_config.clone())?;

    let new_msgs = build_conn_init(dst_chain.clone(), src_chain, opts)?;
    let (key, _) = dst_chain.key_and_signer(opts.signer_seed.clone())?;

    Ok(dst_chain.send_tx(new_msgs, key, "".to_string(), 0)?)
}

#[derive(Clone, Debug)]
pub struct ConnectionOpenOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_client_id: ClientId,
    pub src_client_id: ClientId,
    pub dst_connection_id: ConnectionId,
    pub src_connection_id: ConnectionId,
    pub signer_seed: String,
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
    opts: &ConnectionOpenOptions,
) -> Result<ConnectionEnd, Error> {
    // If there is a connection present on the destination chain, it should look like this:
    let counterparty = Counterparty::new(
        opts.src_client_id.clone(),
        Option::from(opts.src_connection_id.clone()),
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
        opts.dst_client_id.clone(),
        counterparty,
        src_chain.query_compatible_versions()?,
    )
    .unwrap();

    // Retrieve existing connection if any
    let dst_connection =
        dst_chain.query_connection(&opts.dst_connection_id.clone(), ICSHeight::default());

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
                opts.src_connection_id.clone(),
                "missing connection on source chain".to_string(),
            )
            .into());
        }
    }

    check_destination_connection_state(
        opts.dst_connection_id.clone(),
        dst_connection?,
        dst_expected_connection.clone(),
    )?;

    Ok(dst_expected_connection)
}

/// Attempts to build a MsgConnOpenTry.
pub fn build_conn_try(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ConnectionOpenOptions,
) -> Result<Vec<Any>, Error> {
    let dst_expected_connection = validated_expected_connection(
        dst_chain.clone(),
        src_chain.clone(),
        ConnectionMsgType::OpenTry,
        opts,
    )
    .map_err(|e| {
        Kind::ConnOpenTry(
            opts.src_connection_id.clone(),
            "try options inconsistent with existing connection on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_connection = src_chain
        .query_connection(&opts.src_connection_id.clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenTry(
                opts.src_connection_id.clone(),
                "missing connection on source chain".to_string(),
            )
            .context(e)
        })?;

    // TODO - check that the src connection is consistent with the try options

    // TODO - Build add send the message(s) for updating client on source (when we don't need the key seed anymore)
    // TODO - add check if it is required
    // let (key, signer) = src_chain.key_and_signer(&opts.signer_seed)?;
    // build_update_client_and_send(ClientOptions {
    //     dst_client_id: opts.src_client_id.clone(),
    //     dst_chain_config: src_chain.config().clone(),
    //     src_chain_config: dst_chain.config().clone(),
    //     signer_seed: "".to_string(),
    // })?;

    // Get the signer from key seed file
    let (_, signer) = dst_chain.key_and_signer(opts.signer_seed.clone())?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain,
        src_chain.clone(),
        opts.dst_client_id.clone(),
        ics_target_height,
        opts.signer_seed.clone(),
    )?;

    let (client_state, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenTry,
        &opts.src_connection_id.clone(),
        &opts.src_client_id,
        ics_target_height,
    )?;

    let counterparty_versions = if src_connection.versions().is_empty() {
        src_chain.query_compatible_versions()?
    } else {
        src_connection.versions()
    };

    let new_msg = MsgConnectionOpenTry {
        connection_id: opts.dst_connection_id.clone(),
        client_id: opts.dst_client_id.clone(),
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

pub fn build_conn_try_and_send(opts: ConnectionOpenOptions) -> Result<String, Error> {
    // Initialize the source and destination light clients
    let (src_light_client, src_supervisor) =
        TMLightClient::from_config(&opts.src_chain_config, true)?;
    let (dst_light_client, dst_supervisor) =
        TMLightClient::from_config(&opts.dst_chain_config, true)?;

    // Spawn the source and destination light clients
    thread::spawn(move || src_supervisor.run().unwrap());
    thread::spawn(move || dst_supervisor.run().unwrap());

    // Initialize the source and destination chain runtimes
    let src_chain_runtime =
        ChainRuntime::cosmos_sdk(opts.src_chain_config.clone(), src_light_client)?;
    let dst_chain_runtime =
        ChainRuntime::cosmos_sdk(opts.dst_chain_config.clone(), dst_light_client)?;

    let src_chain = src_chain_runtime.handle();
    let dst_chain = dst_chain_runtime.handle();

    let dst_msgs = build_conn_try(dst_chain.clone(), src_chain, &opts)?;
    let (key, _) = dst_chain.key_and_signer(opts.signer_seed)?;

    Ok(dst_chain.send_tx(dst_msgs, key, "".to_string(), 0)?)
}

/// Attempts to build a MsgConnOpenAck.
pub fn build_conn_ack(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ConnectionOpenOptions,
) -> Result<Vec<Any>, Error> {
    let _expected_dst_connection = validated_expected_connection(
        dst_chain.clone(),
        src_chain.clone(),
        ConnectionMsgType::OpenAck,
        opts,
    )
    .map_err(|e| {
        Kind::ConnOpenAck(
            opts.src_connection_id.clone(),
            "ack options inconsistent with existing connection on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_connection = src_chain
        .query_connection(&opts.src_connection_id.clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenAck(
                opts.src_connection_id.clone(),
                "missing connection on source chain".to_string(),
            )
            .context(e)
        })?;

    // TODO - check that the src connection is consistent with the ack options

    // TODO - Build add **send** the message(s) for updating client on source (when we don't need the key seed anymore)
    // TODO - add check if it is required
    // let (key, signer) = src_chain.key_and_signer(&opts.src_signer_seed)?;
    // build_update_client_and_send(ClientOptions {
    //     dst_client_id: opts.src_client_id.clone(),
    //     dst_chain_config: src_chain.config().clone(),
    //     src_chain_config: dst_chain.config().clone(),
    //     signer_seed: "".to_string(),
    // })?;

    // Get the signer from key seed file
    let (_, signer) = dst_chain.key_and_signer(opts.signer_seed.clone())?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain,
        src_chain.clone(),
        opts.dst_client_id.clone(),
        ics_target_height,
        opts.signer_seed.clone(),
    )?;

    let (client_state, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenAck,
        &opts.src_connection_id.clone(),
        &opts.src_client_id,
        ics_target_height,
    )?;

    let new_msg = MsgConnectionOpenAck {
        connection_id: opts.dst_connection_id.clone(),
        counterparty_connection_id: Option::from(opts.src_connection_id.clone()),
        client_state,
        proofs,
        version: src_connection.versions()[0].clone(),
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenAck>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_ack_and_send(opts: ConnectionOpenOptions) -> Result<String, Error> {
    // Initialize the source and destination light clients
    let (src_light_client, src_supervisor) =
        TMLightClient::from_config(&opts.src_chain_config, true)?;
    let (dst_light_client, dst_supervisor) =
        TMLightClient::from_config(&opts.dst_chain_config, true)?;

    // Spawn the source and destination light clients
    thread::spawn(move || src_supervisor.run().unwrap());
    thread::spawn(move || dst_supervisor.run().unwrap());

    // Initialize the source and destination chain runtimes
    let src_chain_runtime =
        ChainRuntime::cosmos_sdk(opts.src_chain_config.clone(), src_light_client)?;
    let dst_chain_runtime =
        ChainRuntime::cosmos_sdk(opts.dst_chain_config.clone(), dst_light_client)?;

    let src_chain = src_chain_runtime.handle();
    let dst_chain = dst_chain_runtime.handle();

    let dst_msgs = build_conn_ack(dst_chain.clone(), src_chain, &opts)?;
    let (key, _) = dst_chain.key_and_signer(opts.signer_seed)?;

    Ok(dst_chain.send_tx(dst_msgs, key, "".to_string(), 0)?)
}

/// Attempts to build a MsgConnOpenConfirm.
pub fn build_conn_confirm(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ConnectionOpenOptions,
) -> Result<Vec<Any>, Error> {
    let _expected_dst_connection = validated_expected_connection(
        dst_chain.clone(),
        src_chain.clone(),
        ConnectionMsgType::OpenAck,
        opts,
    )
    .map_err(|e| {
        Kind::ConnOpenConfirm(
            opts.src_connection_id.clone(),
            "confirm options inconsistent with existing connection on destination chain"
                .to_string(),
        )
        .context(e)
    })?;

    let _src_connection = src_chain
        .query_connection(&opts.src_connection_id.clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenAck(
                opts.src_connection_id.clone(),
                "missing connection on source chain".to_string(),
            )
            .context(e)
        })?;

    // TODO - check that the src connection is consistent with the confirm options

    // Get the signer from key seed file
    let (_, signer) = dst_chain.key_and_signer(opts.signer_seed.clone())?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dst_chain,
        src_chain.clone(),
        opts.dst_client_id.clone(),
        ics_target_height,
        opts.signer_seed.clone(),
    )?;

    let (_, proofs) = src_chain.build_connection_proofs_and_client_state(
        ConnectionMsgType::OpenConfirm,
        &opts.src_connection_id.clone(),
        &opts.src_client_id,
        ics_target_height,
    )?;

    let new_msg = MsgConnectionOpenConfirm {
        connection_id: opts.dst_connection_id.clone(),
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenConfirm>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_confirm_and_send(opts: ConnectionOpenOptions) -> Result<String, Error> {
    // Initialize the source and destination light clients
    let (src_light_client, src_supervisor) =
        TMLightClient::from_config(&opts.src_chain_config, true)?;
    let (dst_light_client, dst_supervisor) =
        TMLightClient::from_config(&opts.dst_chain_config, true)?;

    // Spawn the source and destination light clients
    thread::spawn(move || src_supervisor.run().unwrap());
    thread::spawn(move || dst_supervisor.run().unwrap());

    // Initialize the source and destination chain runtimes
    let src_chain_runtime =
        ChainRuntime::cosmos_sdk(opts.src_chain_config.clone(), src_light_client)?;
    let dst_chain_runtime =
        ChainRuntime::cosmos_sdk(opts.dst_chain_config.clone(), dst_light_client)?;

    let src_chain = src_chain_runtime.handle();
    let dst_chain = dst_chain_runtime.handle();

    let dst_msgs = build_conn_confirm(dst_chain.clone(), src_chain, &opts)?;
    let (key, _) = dst_chain.key_and_signer(opts.signer_seed)?;

    Ok(dst_chain.send_tx(dst_msgs, key, "".to_string(), 0)?)
}
