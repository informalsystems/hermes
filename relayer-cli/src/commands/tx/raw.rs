use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::chain::{Chain, CosmosSDKChain};
use relayer::config::{ChainConfig, Config};
use tendermint::{account::Id, chain::Id as ChainId, net::Address};
use tendermint_rpc::Client;
//use ibc::ics03_connection::msgs::MsgConnectionOpenInit;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::tx_msg::Msg;
use std::str::FromStr;

// Protobuf types
use abscissa_core::component::AsAny;
use ibc_proto::base::crypto::v1beta1::public_key::Sum as PK_Sum;
use ibc_proto::base::crypto::v1beta1::PublicKey;
use ibc_proto::connection::{Counterparty, MsgConnectionOpenInit};
use ibc_proto::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::tx::v1beta1::{AuthInfo, ModeInfo, SignDoc, SignerInfo, Tx, TxBody};

use hex;

// Signer
use k256::{
    ecdsa::{signature::Signer, signature::Verifier, Signature, SigningKey, VerifyKey},
    EncodedPoint, SecretKey,
};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnInitCmd {
    #[options(free, help = "identifier of the local chain")]
    local_chain_id: Option<String>,

    #[options(free, help = "identifier of the remote chain")]
    remote_chain_id: Option<String>,

    #[options(free, help = "identifier of the local client")]
    local_client_id: Option<String>,

    #[options(free, help = "identifier of the remote client")]
    remote_client_id: Option<String>,

    #[options(free, help = "identifier of the local connection")]
    local_connection_id: Option<String>,

    #[options(free, help = "identifier of the remote connection")]
    remote_connection_id: Option<String>,
}

impl TxRawConnInitCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, MsgConnectionOpenInit), String> {
        let local_chain_id = self
            .local_chain_id
            .clone()
            .ok_or_else(|| "missing local chain identifier".to_string())?;

        let local_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == local_chain_id.parse().unwrap())
            .ok_or_else(|| "missing local chain configuration".to_string())?;

        let remote_chain_id = self
            .remote_chain_id
            .clone()
            .ok_or_else(|| "missing remote chain identifier".to_string())?;

        let remote_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == remote_chain_id.parse().unwrap())
            .ok_or_else(|| "missing remote chain configuration".to_string())?;

        let local_client_id = self
            .local_client_id
            .as_ref()
            .ok_or_else(|| "missing local client identifier".to_string())?;

        let local_connection_id = self
            .local_connection_id
            .as_ref()
            .ok_or_else(|| "missing local connection identifier".to_string())?;

        let remote_client_id = self
            .remote_client_id
            .as_ref()
            .ok_or_else(|| "missing remote client identifier".to_string())?;

        let remote_connection_id = self
            .remote_connection_id
            .as_ref()
            .ok_or_else(|| "missing remote connection identifier".to_string())?;

        let remote_prefix =
            CommitmentPrefix::new(remote_chain_config.store_prefix.as_bytes().to_vec());

        // TODO: Hardcode account for now. Figure out a way to retrieve the real account
        let acct = Id::from_str("7C2BB42A8BE69791EC763E51F5A49BCD41E82237").unwrap();

        let cparty = Some(Counterparty {
            client_id: remote_client_id.to_string(),
            connection_id: remote_connection_id.to_string(),
            prefix: None, // TODO Use a MerklePrefix
        });

        let msg = MsgConnectionOpenInit {
            client_id: local_client_id.to_string(),
            connection_id: local_connection_id.to_string(),
            counterparty: cparty,
            signer: acct.as_bytes().to_vec(),
        };

        //     local_connection_id.to_string(),
        //     local_client_id.to_string(),
        //     remote_connection_id.to_string(),
        //     remote_client_id.to_string(),
        //     remote_prefix,
        //     signer
        // );

        //TODO handle result better
        Ok((local_chain_config.clone(), msg))
    }
}

// convenience function to get address from private key
// TODO: simplify and move ?
fn get_account(pk: Vec<u8>) -> Vec<u8> {
    use crypto::digest::Digest;
    use crypto::ripemd160::Ripemd160;
    use crypto::sha2::Sha256;
    let mut seed = Sha256::new();
    seed.input(pk.as_slice());
    let mut bytes = vec![0; seed.output_bytes()];
    seed.result(&mut bytes);

    let mut hash = Ripemd160::new();
    hash.input(bytes.as_slice());
    let mut acct = vec![0; hash.output_bytes()];
    hash.result(&mut acct);
    acct.to_vec()
}

impl Runnable for TxRawConnInitCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, msg) = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", msg);

        // Create chain
        let chain = CosmosSDKChain::from_config(chain_config.clone()).unwrap();

        // This is a pregenerated private key from running:
        //      let signing_key = SigningKey::random(&mut OsRng);
        //      println!("{:?", hex::encode(signing_key.to_bytes()));
        // It corresponds to the address: cosmos14kl05amnc3mdyj5d2r27agvwhuqgz7vwfz0wwj
        // Add it to your genesis or send coins to it.
        // Then query the account number and update account_number here.
        let signing_key_bytes = "cda4e48a1ae228656e483b2f3ae7bca6d04abcef64189ff56d481987259dd2a4";
        let account_number = 12;

        let signing_key = SigningKey::new(&hex::decode(signing_key_bytes).unwrap()).unwrap();
        let verify_key = VerifyKey::from(&signing_key);
        let pubkey_bytes = verify_key.to_bytes().to_vec();
        let addr = get_account(pubkey_bytes.clone());
        msg.signer = addr; // XXX: replace signer

        // Build and sign transaction
        //let _signed = chain.build_sign_tx(vec![Box::new(msg)]);

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

        let sum = Some(PK_Sum::Secp256k1(pubkey_bytes));

        let pk = Some(PublicKey { sum });

        let single = Single { mode: 1 };
        let sum_single = Some(Sum::Single(single));
        let mode = Some(ModeInfo { sum: sum_single });

        let signer_info = SignerInfo {
            public_key: pk,
            mode_info: mode,
            sequence: 0,
        };

        let auth_info = AuthInfo {
            signer_infos: vec![signer_info],
            fee: None,
        };

        // A protobuf serialization of a TxBody
        let mut body_buf = Vec::new();
        prost::Message::encode(&body, &mut body_buf).unwrap();

        // A protobuf serialization of a AuthInfo
        let mut auth_buf = Vec::new();
        prost::Message::encode(&auth_info, &mut auth_buf).unwrap();

        let sign_doc = SignDoc {
            body_bytes: body_buf.clone(),
            auth_info_bytes: auth_buf.clone(),
            chain_id: chain_config.clone().id.to_string(),
            account_number: account_number,
        };

        // A protobuf serialization of a AuthInfo
        let mut signdoc_buf = Vec::new();
        prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

        let signature: Signature = signing_key.sign(&signdoc_buf);

        status_info!("Signed Tx", "{:?}", signed_doc);

        let tx_raw = TxRaw {
            body_bytes,
            auth_info_bytes: auth_bytes,
            signatures: vec![signature.as_ref().to_vec()],
        };

        let mut txraw_buf = Vec::new();
        prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();
        println!("{:?}", txraw_buf);

        /*
        // TODO: get this from the config
        let client = Client::new(Address::Tcp{
            peer_id: None,
            host: "localhost",
            port: 26657,
        });
        match client.broadcast_tx_commit(Transaction::new(txraw_buf)); {
            Ok(resp) => println!("OK! {:?}", resp),
            Err(e) => println!("Err {:?}", e)
        };*/
    }
}
