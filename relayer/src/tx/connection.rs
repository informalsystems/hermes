use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};
use bitcoin::hashes::hex::ToHex;
use ibc::ics03_connection::connection::Counterparty;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::tx_msg::Msg;
use prost_types::Any;
use serde_json::Value;
use std::str::FromStr;
use tendermint::account::Id as AccountId;
use tendermint_rpc::Id;

#[derive(Clone, Debug)]
pub struct ConnectionOpenInitOptions {
    pub src_client_id: ClientId,
    pub dest_client_id: ClientId,
    pub src_connection_id: ConnectionId,
    pub dest_connection_id: Option<ConnectionId>,
    pub src_chain_config: ChainConfig,
    pub dest_chain_config: ChainConfig,
    pub signer_seed: String,
    pub account_sequence: u64,
}

pub fn conn_init(opts: ConnectionOpenInitOptions) -> Result<Vec<u8>, Error> {
    // Get the destination chain
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Get the key and signer from key seed file
    let (key, signer) = dest_chain.key_and_signer(&opts.signer_seed)?;

    let counterparty = Counterparty::new(
        opts.dest_client_id,
        opts.dest_connection_id,
        CommitmentPrefix::from(dest_chain.config().store_prefix.as_bytes().to_vec()),
    );

    let new_msg = MsgConnectionOpenInit {
        client_id: opts.src_client_id,
        connection_id: opts.src_connection_id,
        counterparty: counterparty.unwrap(),
        version: "".to_string(),
        signer,
    };

    let mut proto_msgs: Vec<Any> = Vec::new();

    let any_msg = Any {
        type_url: "/ibc.core.connection.v1.MsgConnectionOpenInit".to_string(),
        value: new_msg.get_sign_bytes(),
    };

    // Add proto message
    proto_msgs.push(any_msg);

    let response = dest_chain.send(proto_msgs, key, opts.account_sequence, "".to_string(), 0)?;

    Ok(response)
}
