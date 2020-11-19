use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use std::thread;
use std::time::Duration;

use prost_types::Any;
use serde_json::Value;

use bitcoin::hashes::hex::ToHex;

use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::msgs::ConnectionMsgType;
use ibc::ics03_connection::version::get_compatible_versions;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};
use crate::tx::client::{build_update_client, build_update_client_and_send, ClientOptions};

#[derive(Clone, Debug)]
pub struct ConnectionOpenInitOptions {
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dest_client_id: ClientId,
    pub src_client_id: ClientId,
    pub dest_connection_id: ConnectionId,
    pub src_connection_id: Option<ConnectionId>,
}

pub fn build_conn_init(
    dest_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    opts: &ConnectionOpenInitOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the connection
    if dest_chain
        .query_connection(&opts.dest_connection_id, ICSHeight::default())
        .is_ok()
    {
        return Err(Kind::ConnOpenInit(
            opts.dest_connection_id.clone(),
            "connection already exist".into(),
        )
        .into());
    }

    // Get signer
    let signer = dest_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let prefix = src_chain.query_commitment_prefix()?;

    let counterparty = Counterparty::new(
        opts.src_client_id.clone(),
        opts.src_connection_id.clone(),
        prefix,
    );

    // Build the domain type message
    let new_msg = MsgConnectionOpenInit {
        client_id: opts.dest_client_id.clone(),
        connection_id: opts.dest_connection_id.clone(),
        counterparty,
        version: dest_chain.query_compatible_versions()?[0].clone(),
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgConnectionOpenInit>()])
}

pub fn build_conn_init_and_send(opts: &ConnectionOpenInitOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let dest_chain = &mut CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let new_msgs = build_conn_init(dest_chain, src_chain, opts)?;
    let key = dest_chain
        .keybase()
        .get_key()
        .map_err(|e| Kind::KeyBase.context("failed to retrieve key"))?;

    Ok(dest_chain.send(new_msgs, key, "".to_string(), 0)?)
}

#[derive(Clone, Debug)]
pub struct ConnectionOpenTryOptions {
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dest_client_id: ClientId,
    pub src_client_id: ClientId,
    pub dest_connection_id: ConnectionId,
    pub src_connection_id: ConnectionId,
}

fn check_connection_state_for_try(
    connection_id: ConnectionId,
    existing_connection: ConnectionEnd,
    expected_connection: ConnectionEnd,
) -> Result<(), Error> {
    if existing_connection.client_id() != expected_connection.client_id()
        || existing_connection.counterparty().client_id()
            != expected_connection.counterparty().client_id()
        || existing_connection.counterparty().connection_id().is_some()
            && existing_connection.counterparty().connection_id()
                != expected_connection.counterparty().connection_id()
    {
        Err(Kind::ConnOpenTry(
            connection_id,
            "connection already exist in an incompatible state".into(),
        )
        .into())
    } else {
        Ok(())
    }
}

/// Attempts to send a MsgConnOpenTry to the dest_chain.
pub fn build_conn_try(
    dest_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    opts: &ConnectionOpenTryOptions,
) -> Result<Vec<Any>, Error> {
    // If there is a connection present on the destination chain it should look like this
    let counterparty = Counterparty::new(
        opts.src_client_id.clone(),
        Some(opts.src_connection_id.clone()),
        src_chain.query_commitment_prefix()?,
    );
    let dest_expected_connection = ConnectionEnd::new(
        State::Init,
        opts.dest_client_id.clone(),
        counterparty.clone(),
        src_chain.query_compatible_versions()?,
    )
    .unwrap();

    // Check that if a connection exists on destination it is consistent with the try options
    if let Ok(dest_connection) =
        dest_chain.query_connection(&opts.dest_connection_id.clone(), ICSHeight::default())
    {
        check_connection_state_for_try(
            opts.dest_connection_id.clone(),
            dest_connection,
            dest_expected_connection,
        )?
    }

    let src_connection = src_chain
        .query_connection(&opts.src_connection_id.clone(), ICSHeight::default())
        .map_err(|e| {
            Kind::ConnOpenTry(
                opts.src_connection_id.clone(),
                "missing connection on source chain".to_string(),
            )
        })?;
    // TODO - check that the src connection is consistent with the try options

    // TODO - Build add send the message(s) for updating client on source (when we don't need the key seed anymore)
    // TODO - add check if it is required
    // let (key, signer) = src_chain.key_and_signer(&opts.signer_seed)?;
    // build_update_client_and_send(ClientOptions {
    //     dest_client_id: opts.src_client_id.clone(),
    //     dest_chain_config: src_chain.config().clone(),
    //     src_chain_config: dest_chain.config().clone(),
    //     signer_seed: "".to_string(),
    // })?;

    // Get signer
    let signer = dest_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build message(s) for updating client on destination
    let ics_target_height = src_chain.query_latest_height()?;

    let mut msgs = build_update_client(
        dest_chain,
        src_chain,
        opts.dest_client_id.clone(),
        ics_target_height,
    )?;

    let client_state = src_chain.query_client_state(&opts.src_client_id, ics_target_height)?;

    let proofs = src_chain.build_connection_proofs(
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
        connection_id: opts.dest_connection_id.clone(),
        client_id: opts.dest_client_id.clone(),
        client_state: Some(client_state),
        counterparty_chosen_connection_id: src_connection.counterparty().connection_id().cloned(),
        counterparty,
        counterparty_versions,
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgConnectionOpenTry>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_conn_try_and_send(opts: ConnectionOpenTryOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.src_chain_config.clone())?;
    let dest_chain = &mut CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let dest_msgs = build_conn_try(dest_chain, src_chain, &opts)?;
    let key = dest_chain
        .keybase()
        .get_key()
        .map_err(|e| Kind::KeyBase.context(e))?;

    Ok(dest_chain.send(dest_msgs, key, "".to_string(), 0)?)
}
