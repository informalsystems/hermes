use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use hex;
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

pub fn conn_init(opts: ConnectionOpenInitOptions) -> Result<Vec<u8>, Error> {
    // Get the destination chain
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let id_hex = "25EF56CA795135E409368E6DB8110F22A4BE05C2";
    let signer = AccountId::from_str(id_hex).unwrap();

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

   let msg_type = "/ibc.connection.MsgConnectionOpenInit".to_string();

    // Send message
    let response = dest_chain.send(msg_type, msg.get_sign_bytes(), "".to_string(), 0)
        .map_err(|e| Kind::MessageTransaction("failed to initialize open connection".to_string()).context(e))?;

    Ok(response)
}
