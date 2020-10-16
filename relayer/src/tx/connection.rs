use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::Error;
use ibc::ics03_connection::connection::Counterparty;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::tx_msg::Msg;
use prost_types::Any;
use std::str::FromStr;
use tendermint::account::Id as AccountId;

#[derive(Clone, Debug)]
pub struct ConnectionOpenInitOptions {
    pub src_client_id: ClientId,
    pub dest_client_id: ClientId,
    pub src_connection_id: ConnectionId,
    pub dest_connection_id: ConnectionId,
    pub src_chain_config: ChainConfig,
    pub dest_chain_config: ChainConfig,
}

pub fn conn_init(opts: ConnectionOpenInitOptions) -> Result<(), Error> {
    // Get the destination chain
    let dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let id_hex = "25EF56CA795135E409368E6DB8110F22A4BE05C2";
    let signer = AccountId::from_str(id_hex).unwrap();

    // let signer = Id::from_str(dest_chain.config().account_prefix.as_str()).map_err(|e| {
    //     Kind::MessageTransaction("Connection Open Init Error: Bad Signer".into()).context(e)
    // })?;

    let counterparty = Counterparty::new(
        opts.dest_client_id,
        opts.dest_connection_id,
        CommitmentPrefix::from(vec![]),
    );

    let msg = MsgConnectionOpenInit {
        client_id: opts.src_client_id,
        connection_id: opts.src_connection_id,
        counterparty: counterparty.unwrap(),
        // TODO - add to opts
        version: "1.0.0".to_string(),
        signer,
    };

    // Create a proto any message
    let mut proto_msgs: Vec<Any> = Vec::new();

    let any_msg = Any {
        type_url: "/ibc.connection.MsgConnectionOpenInit".to_string(), // "type.googleapis.com/ibc.connection.MsgConnectionOpenInit".to_string(),
        value: msg.get_sign_bytes(),
    };

    // Add proto message
    proto_msgs.push(any_msg);

    // Send message
    dest_chain.send(&proto_msgs)
}
