use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc_proto::connection::{Counterparty, MsgConnectionOpenInit};
use ibc_proto::tx::v1beta1::TxBody;
use std::str::FromStr;
use tendermint::account::Id;

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

    let signer = Id::from_str(dest_chain.config().account_prefix.as_str()).map_err(|e| {
        Kind::MessageTransaction("Connection Open Init: Bad Signer".into()).context(e)
    })?;

    let counterparty = Some(Counterparty {
        client_id: opts.dest_client_id.to_string(),
        connection_id: opts.dest_connection_id.to_string(),
        prefix: None, // TODO Use a MerklePrefix
    });

    // MsgConnectionOpenInit protobuf message
    let msg = MsgConnectionOpenInit {
        client_id: opts.src_client_id.to_string(),
        connection_id: opts.src_connection_id.to_string(),
        counterparty,
        signer: signer.as_bytes().to_vec(),
    };

    let mut proto_msgs: Vec<prost_types::Any> = Vec::new();
    let mut buf = Vec::new();

    // Have a loop if new_builder takes more messages
    // for now just encode one message
    prost::Message::encode(&msg, &mut buf).unwrap();

    // Create a proto any message
    let any_msg = prost_types::Any {
        type_url: "/ibc.connection.MsgConnectionOpenInit".to_string(), // "type.googleapis.com/ibc.connection.MsgConnectionOpenInit".to_string(),
        value: buf,
    };

    // Add proto message
    proto_msgs.push(any_msg);

    // Create TxBody
    let body = TxBody {
        messages: proto_msgs,
        memo: "".to_string(),
        timeout_height: 0,
        extension_options: Vec::<prost_types::Any>::new(),
        non_critical_extension_options: Vec::<prost_types::Any>::new(),
    };

    // A protobuf serialization of a TxBody
    let mut body_buf = Vec::new();
    prost::Message::encode(&body, &mut body_buf).unwrap();

    // TODO: move this logic to tx builder
    // let sum = Some(PK_Sum::Secp256k1(pubkey_bytes));
    //
    // let pk = Some(PublicKey { sum });
    //
    // let single = Single { mode: 1 };
    // let sum_single = Some(Sum::Single(single));
    // let mode = Some(ModeInfo { sum: sum_single });
    //
    // let signer_info = SignerInfo {
    //     public_key: pk,
    //     mode_info: mode,
    //     sequence: 0,
    // };
    //
    // let auth_info = AuthInfo {
    //     signer_infos: vec![signer_info],
    //     fee: None,
    // };
    //
    // // A protobuf serialization of a AuthInfo
    // let mut auth_buf = Vec::new();
    // prost::Message::encode(&auth_info, &mut auth_buf).unwrap();
    //
    // let sign_doc = SignDoc {
    //     body_bytes: body_buf.clone(),
    //     auth_info_bytes: auth_buf.clone(),
    //     chain_id: chain_config.clone().id.to_string(),
    //     account_number: account_number,
    // };
    //
    // // A protobuf serialization of a AuthInfo
    // let mut signdoc_buf = Vec::new();
    // prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();
    //
    // let signature: Signature = signing_key.sign(&signdoc_buf);
    //
    // status_info!("Signed Tx", "{:?}", signed_doc);
    //
    // let tx_raw = TxRaw {
    //     body_bytes,
    //     auth_info_bytes: auth_bytes,
    //     signatures: vec![signature.as_ref().to_vec()],
    // };
    //
    // let mut txraw_buf = Vec::new();
    // prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();
    // println!("{:?}", txraw_buf);

    Ok(())
}
