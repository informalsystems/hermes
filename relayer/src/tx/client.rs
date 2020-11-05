use bitcoin::hashes::hex::ToHex;
use prost_types::Any;
use std::convert::TryInto;
use std::time::Duration;

use ibc::downcast;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use std::str::FromStr;

use tendermint::account::Id as AccountId;
use tendermint_light_client::types::TrustThreshold;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::height::Height;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
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
pub struct ClientOptions {
    pub dest_client_id: ClientId,
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_seed: String,
    pub account_sequence: u64,
}

pub fn create_client(opts: ClientOptions) -> Result<Vec<u8>, Error> {
    // Get the source and destination chains.
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Verify that the client has not been created already, i.e the destination chain does not
    // have a state for this client.
    let client_state = dest_chain.query_client_state(&opts.dest_client_id, 0_u32.into(), false);
    if client_state.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            opts.dest_client_id,
            "client already exists".into(),
        )));
    }

    // Get the key and signer from key seed file.
    let (key, signer) = dest_chain.key_and_signer(&opts.signer_seed)?;

    // Build client create message with the data from the source chain at latest height.
    let latest_height = src_chain.query_latest_height()?;
    let new_msg = MsgCreateAnyClient::new(
        opts.dest_client_id,
        src_chain.build_client_state(latest_height)?,
        src_chain.build_consensus_state(latest_height)?,
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?;

    let proto_msgs: Vec<Any> = vec![new_msg.to_any::<RawMsgCreateClient>()];

    // Send the transaction to the destination chain
    Ok(dest_chain.send(proto_msgs, key, opts.account_sequence, "".to_string(), 0)?)
}

pub fn update_client(opts: ClientOptions) -> Result<Vec<u8>, Error> {
    // Get the source and destination chains
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Get the latest trusted height from the client state on destination.
    let trusted_height = dest_chain
        .query_client_state(&opts.dest_client_id, 0_u32.into(), false)?
        .latest_height();

    // Set the target height to latest.
    let target_height = src_chain.query_latest_height()?;

    // Get the key and signer from key seed file.
    let (key, signer) = dest_chain.key_and_signer(&opts.signer_seed)?;

    let new_msg = MsgUpdateAnyClient {
        client_id: opts.dest_client_id,
        header: src_chain.build_header(trusted_height, target_height)?,
        signer,
    };

    let proto_msgs: Vec<Any> = vec![new_msg.to_any::<RawMsgUpdateClient>()];

    Ok(dest_chain.send(proto_msgs, key, opts.account_sequence, "".to_string(), 0)?)
}
