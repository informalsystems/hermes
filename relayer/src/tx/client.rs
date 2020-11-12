use std::str::FromStr;
use std::time::Duration;
use std::{convert::TryInto, thread};

use bitcoin::hashes::hex::ToHex;
use prost_types::Any;

use tendermint::account::Id as AccountId;
use tendermint_light_client::types::TrustThreshold;
use tendermint_proto::DomainType;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::header::Header;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::ClientState;
use ibc::ics02_client::state::ConsensusState;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics24_host::Path::ClientConsensusState;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::{handle::ChainHandle, runtime::ChainRuntime, Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};
use crate::light_client::tendermint::LightClient as TMLightClient;

#[derive(Clone, Debug)]
pub struct ClientOptions {
    pub dst_client_id: ClientId,
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_seed: String,
}

pub fn build_create_client(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    dst_client_id: ClientId,
    signer_seed: String,
) -> Result<MsgCreateAnyClient, Error> {
    // Verify that the client has not been created already, i.e the dstination chain does not
    // have a state for this client.
    let client_state = dst_chain.query_client_state(&dst_client_id, Height::default());
    if client_state.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            dst_client_id,
            "client already exists".into(),
        )));
    }

    // Get the key and signer from key seed file.
    let (key, signer) = dst_chain.key_and_signer(signer_seed)?;

    // Build client create message with the data from source chain at latest height.
    let latest_height = src_chain.query_latest_height()?;
    Ok(MsgCreateAnyClient::new(
        dst_client_id,
        src_chain.build_client_state(latest_height)?.wrap_any(),
        src_chain.build_consensus_state(latest_height)?.wrap_any(),
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?)
}

pub fn build_create_client_and_send(opts: ClientOptions) -> Result<String, Error> {
    // Initialize the source and dstination light clients
    let (src_light_client, src_supervisor) =
        TMLightClient::from_config(&opts.src_chain_config, true)?;
    let (dst_light_client, dst_supervisor) =
        TMLightClient::from_config(&opts.dst_chain_config, true)?;

    // Spawn the source and dstination light clients
    thread::spawn(move || src_supervisor.run().unwrap());
    thread::spawn(move || dst_supervisor.run().unwrap());

    // Initialize the source and dstination chain runtimes
    let src_chain_runtime = ChainRuntime::cosmos_sdk(opts.src_chain_config, src_light_client)?;
    let dst_chain_runtime = ChainRuntime::cosmos_sdk(opts.dst_chain_config, dst_light_client)?;

    let src_chain = src_chain_runtime.handle();
    let dst_chain = dst_chain_runtime.handle();

    let new_msg = build_create_client(
        dst_chain.clone(),
        src_chain,
        opts.dst_client_id,
        opts.signer_seed.clone(),
    )?;

    let (key, _) = dst_chain.key_and_signer(opts.signer_seed)?;

    Ok(dst_chain.send_tx(
        vec![new_msg.to_any::<RawMsgCreateClient>()],
        key,
        "".to_string(),
        0,
    )?)
}

pub fn build_update_client(
    dst_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    dst_client_id: ClientId,
    target_height: Height,
    signer_seed: &str,
) -> Result<Vec<Any>, Error> {
    // Get the latest trusted height from the client state on dstination.
    let trusted_height = dst_chain
        .query_client_state(&dst_client_id, Height::default())?
        .latest_height();

    // Get the key and signer from key seed file.
    let (key, signer) = dst_chain.key_and_signer(signer_seed)?;

    let new_msg = MsgUpdateAnyClient {
        client_id: dst_client_id,
        header: src_chain
            .build_header(trusted_height, target_height)?
            .wrap_any(),
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgUpdateClient>()])
}

pub fn build_update_client_and_send(opts: ClientOptions) -> Result<String, Error> {
    // Get the source and dstination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let dst_chain = &mut CosmosSDKChain::from_config(opts.clone().dst_chain_config)?;

    let target_height = src_chain.query_latest_height()?;
    let new_msgs = build_update_client(
        dst_chain,
        src_chain,
        opts.dst_client_id,
        target_height,
        &opts.signer_seed,
    )?;
    let (key, _) = dst_chain.key_and_signer(&opts.signer_seed)?;

    Ok(dst_chain.send(new_msgs, key, "".to_string(), 0)?)
}
