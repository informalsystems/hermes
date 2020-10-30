use bitcoin::hashes::hex::ToHex;
use prost_types::Any;
use std::convert::TryInto;
use std::time::Duration;

use ibc::downcast;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use std::str::FromStr;

use tendermint::account::Id as AccountId;
use tendermint::trust_threshold::TrustThresholdFraction;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;

use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::height::Height;
use ibc::ics02_client::msgs::MsgCreateAnyClient;
use ibc::ics02_client::msgs::MsgUpdateAnyClient;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics24_host::Path::ClientConsensusState;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::tx_msg::Msg;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

use crate::keyring::store::{KeyEntry, KeyRingOperations};
use tendermint_proto::DomainType;

#[derive(Clone, Debug)]
pub struct CreateClientOptions {
    pub dest_client_id: ClientId,
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_key: String,
    pub account_sequence: u64,
}

pub fn create_client(opts: CreateClientOptions) -> Result<Vec<u8>, Error> {
    // Get the source and destination chains.
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Query the client state on destination chain.
    let last_state = dest_chain.query_client_state(&opts.dest_client_id);
    if last_state.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            opts.dest_client_id,
            "client already exists".into(),
        )));
    }

    // Get the latest header from the source chain and build the consensus state.
    let tm_latest_header = src_chain.query_latest_header()?;
    let tm_consensus_params = src_chain.query_consensus_params()?;

    // Build the consensus state.
    let consensus_state = AnyConsensusState::Tendermint(TendermintConsensusState::from(
        tm_latest_header.signed_header.header().clone(),
    ));

    let height = u64::from(tm_latest_header.signed_header.header().height);
    let version = tm_latest_header.signed_header.header().chain_id.to_string();

    // TODO get this from the configuration
    let trust_level = TrustThresholdFraction {
        numerator: 1,
        denominator: 3,
    };

    // Build the client state.
    let client_state = ibc::ics07_tendermint::client_state::ClientState::new(
        src_chain.id().to_string(),
        trust_level,
        src_chain.trusting_period(),
        src_chain.unbonding_period(),
        Duration::from_millis(3000),
        Height::new(ChainId::chain_version(version.clone()), height),
        tm_consensus_params,
        Height::new(ChainId::chain_version(version), 0),
        "upgrade/upgradedClient".to_string(),
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

    // Get the key and signer from key seed file.
    let (key, signer) = dest_chain.key_and_signer(&opts.signer_key)?;

    // Build the domain type message.
    let new_msg =
        MsgCreateAnyClient::new(opts.dest_client_id, client_state, consensus_state, signer)
            .map_err(|e| {
                Kind::MessageTransaction("failed to build the create client message".into())
                    .context(e)
            })?;

    let msg_type = "/ibc.core.client.v1.MsgCreateClient".to_string();

    let response = dest_chain.send(
        msg_type,
        new_msg.get_sign_bytes(),
        key,
        opts.account_sequence,
        "".to_string(),
        0,
    )?;

    Ok(response)
}

#[derive(Clone, Debug)]
pub struct UpdateClientOptions {
    pub dest_client_id: ClientId,
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_key: String,
    pub account_sequence: u64,
}

pub fn update_client(opts: UpdateClientOptions) -> Result<Vec<u8>, Error> {
    // Get the source and destination chains
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Get the last header from source chain and verify it.
    // TODO - add client verification
    let latest_header = src_chain.query_latest_header()?;

    // Get the client state from the destination chain
    let last_state = dest_chain.query_client_state(&opts.dest_client_id)?;

    // Get the latest trusted height from the last client state on destination.
    // TODO - add client verification
    let chain_trusted_height = last_state
        .latest_height()
        .version_height
        .try_into()
        .map_err(|_| Kind::Query)?;
    // Get the trusted header from the source chain.
    let chain_trusted_header = src_chain.query_header_at_height(chain_trusted_height)?;

    // Create the ics07 Header to be included in the MsgUpdateClient.
    let header = AnyHeader::Tendermint(TendermintHeader {
        signed_header: latest_header.signed_header,
        validator_set: latest_header.validators,
        trusted_height: last_state.latest_height(),
        trusted_validator_set: chain_trusted_header.validators,
    });

    // Get the key and signer from key seed file.
    let (key, signer) = dest_chain.key_and_signer(&opts.signer_key)?;

    // Build the domain type message.
    let new_msg = MsgUpdateAnyClient::new(opts.dest_client_id, header, signer);
    let msg_type = "/ibc.core.client.v1.MsgUpdateClient".to_string();

    let response = dest_chain.send(
        msg_type,
        new_msg.get_sign_bytes(),
        key,
        opts.account_sequence,
        "".to_string(),
        0,
    )?;

    Ok(response)
}
