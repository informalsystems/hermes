use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRingOperations};
use bitcoin::hashes::hex::ToHex;
use futures::SinkExt;
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
}

pub fn conn_init(opts: ConnectionOpenInitOptions) -> Result<Vec<u8>, Error> {
    // Get the destination chain
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Retrieve the key specified in the config file
    let key_name = dest_chain.config();
    let key = dest_chain
        .keybase
        .get(key_name.key_name.clone())
        .map_err(|e| Kind::KeyBase.context("failed to retrieve the key"))?;

    let signer: AccountId =
        AccountId::from_str(&key.address.to_hex()).map_err(|e| Kind::KeyBase.context(e))?;

    let counterparty = Counterparty::new(
        opts.dest_client_id,
        opts.dest_connection_id,
        CommitmentPrefix::from(dest_chain.config().store_prefix.clone().as_bytes().to_vec()),
    );

    let msg = MsgConnectionOpenInit {
        client_id: opts.src_client_id,
        connection_id: opts.src_connection_id,
        counterparty: counterparty.unwrap(),
        version: "".to_string(),
        signer,
    };

    let msg_type = "/ibc.core.connection.v1.MsgConnectionOpenInit".to_string();

    // Send message
    let response = dest_chain
        .send(msg_type, msg.get_sign_bytes(), key, "".to_string(), 0)
        .map_err(|e| {
            Kind::MessageTransaction("failed to initialize open connection".to_string()).context(e)
        })?;

    Ok(response)
}
