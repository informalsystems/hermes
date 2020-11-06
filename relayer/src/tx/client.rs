use prost_types::Any;
use std::time::Duration;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::msgs::MsgCreateAnyClient;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::tx_msg::Msg;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};
use crate::util::block_on;
use bitcoin::hashes::hex::ToHex;
use ibc::ics02_client::height::Height;
use std::str::FromStr;
use tendermint::account::Id as AccountId;

#[derive(Clone, Debug)]
pub struct CreateClientOptions {
    pub dest_client_id: ClientId,
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_key: String,
}

pub fn create_client(opts: CreateClientOptions) -> Result<Vec<u8>, Error> {
    // Get the destination chain
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Get the key from key seed file
    let key = dest_chain
        .keybase
        .key_from_seed_file(&opts.signer_key)
        .map_err(|e| Kind::KeyBase.context(e))?;
    let signer: AccountId =
        AccountId::from_str(&key.address.to_hex()).map_err(|e| Kind::KeyBase.context(e))?;

    // Query the client state on destination chain.
    let response = dest_chain.query(
        ClientStatePath(opts.clone().dest_client_id),
        tendermint::block::Height::from(0_u32),
        false,
    );

    if response.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            opts.dest_client_id,
            "client already exists".into(),
        )));
    }

    // Get the latest header from the source chain and build the consensus state.
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let tm_latest_header = src_chain.query_latest_header().map_err(|e| {
        Kind::CreateClient(
            opts.dest_client_id.clone(),
            "failed to get the latest header".into(),
        )
        .context(e)
    })?;

    let height = u64::from(tm_latest_header.signed_header.header.height);
    let version = tm_latest_header.signed_header.header.chain_id.to_string();

    let tm_consensus_state = ibc::ics07_tendermint::consensus_state::ConsensusState::from(
        tm_latest_header.signed_header,
    );

    let any_consensus_state = AnyConsensusState::Tendermint(tm_consensus_state);

    // Build the client state.
    let any_client_state = ibc::ics07_tendermint::client_state::ClientState::new(
        src_chain.id().to_string(),
        src_chain.config().trusting_period,
        src_chain.unbonding_period(),
        Duration::from_millis(3000),
        Height::new(ChainId::chain_version(version.clone()), height),
        Height::new(ChainId::chain_version(version), 0),
        "".to_string(),
        false,
        false,
    )
    .map_err(|e| {
        Kind::CreateClient(
            opts.dest_client_id.clone(),
            "failed to build the client state".into(),
        )
        .context(e)
    })
    .map(AnyClientState::Tendermint)?;

    let signer = dest_chain.config().account_prefix.parse().map_err(|e| {
        Kind::CreateClient(opts.dest_client_id.clone(), "bad signer".into()).context(e)
    })?;

    // Build the domain type message
    let new_msg = MsgCreateAnyClient::new(
        opts.dest_client_id,
        any_client_state,
        any_consensus_state,
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?;

    let msg_type = "/ibc.client.MsgCreateClient".to_ascii_lowercase();

    // TODO - Replace logic to fetch the proper account sequence via CLI parameter
    let response = dest_chain
        .send(msg_type, new_msg.get_sign_bytes(), &key, "".to_string(), 0)
        .map_err(|e| Kind::MessageTransaction("failed to create client".to_string()).context(e))?;

    Ok(response)
}
