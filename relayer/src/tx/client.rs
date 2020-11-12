use std::convert::TryInto;
use std::str::FromStr;
use std::time::Duration;

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

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};

#[derive(Clone, Debug)]
pub struct ClientOptions {
    pub dest_client_id: ClientId,
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_seed: String,
}

pub fn build_create_client(
    dest_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    dest_client_id: ClientId,
    signer_seed: &str,
) -> Result<MsgCreateAnyClient, Error> {
    // Verify that the client has not been created already, i.e the destination chain does not
    // have a state for this client.
    let client_state = dest_chain.query_client_state(&dest_client_id, Height::default());
    if client_state.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            dest_client_id,
            "client already exists".into(),
        )));
    }

    // Get the key and signer from key seed file.
    let (key, signer) = dest_chain.key_and_signer(signer_seed)?;

    // Build client create message with the data from source chain at latest height.
    let latest_height = src_chain.query_latest_height()?;
    Ok(MsgCreateAnyClient::new(
        dest_client_id,
        src_chain.build_client_state(latest_height)?.wrap_any(),
        src_chain.build_consensus_state(latest_height)?.wrap_any(),
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?)
}

pub fn build_create_client_and_send(opts: ClientOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let dest_chain = &mut CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let new_msg = build_create_client(
        dest_chain,
        src_chain,
        opts.dest_client_id,
        &opts.signer_seed,
    )?;
    let (key, _) = dest_chain.key_and_signer(&opts.signer_seed)?;

    Ok(dest_chain.send(
        vec![new_msg.to_any::<RawMsgCreateClient>()],
        key,
        "".to_string(),
        0,
    )?)
}

pub fn build_update_client(
    dest_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    dest_client_id: ClientId,
    target_height: Height,
    signer_seed: &str,
) -> Result<Vec<Any>, Error> {
    // Get the latest trusted height from the client state on destination.
    let trusted_height = dest_chain
        .query_client_state(&dest_client_id, Height::default())?
        .latest_height();

    // Get the key and signer from key seed file.
    let (key, signer) = dest_chain.key_and_signer(signer_seed)?;

    let new_msg = MsgUpdateAnyClient {
        client_id: dest_client_id,
        header: src_chain
            .build_header(trusted_height, target_height)?
            .wrap_any(),
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgUpdateClient>()])
}

pub fn build_update_client_and_send(opts: ClientOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let dest_chain = &mut CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let target_height = src_chain.query_latest_height()?;
    let new_msgs = build_update_client(
        dest_chain,
        src_chain,
        opts.dest_client_id,
        target_height,
        &opts.signer_seed,
    )?;
    let (key, _) = dest_chain.key_and_signer(&opts.signer_seed)?;

    Ok(dest_chain.send(new_msgs, key, "".to_string(), 0)?)
}
