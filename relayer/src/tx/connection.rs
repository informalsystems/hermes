use prost_types::Any;
use serde_json::Value;
use std::str::FromStr;

use bitcoin::hashes::hex::ToHex;

use tendermint::account::Id as AccountId;
use tendermint_rpc::Id;

use ibc::ics03_connection::connection::Counterparty;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::tx_msg::Msg;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenInit as RawMsgConnectionOpenInit;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};

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
    // Get the source and destination chains
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Get the key and signer from key seed file
    let (key, signer) = dest_chain.key_and_signer(&opts.signer_seed)?;

    let prefix = src_chain.query_commitment_prefix()?;

    let new_msg = dest_chain.build_conn_open_init_msg(opts.clone(), prefix, signer)?;

    let proto_msgs: Vec<Any> = vec![new_msg.to_any::<RawMsgConnectionOpenInit>()];

    Ok(dest_chain.send(proto_msgs, key, opts.account_sequence, "".to_string(), 0)?)
}
