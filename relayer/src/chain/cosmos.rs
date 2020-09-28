use prost_types::Any;
use std::str::FromStr;
use std::time::Duration;

use tendermint::abci::Path as TendermintABCIPath;
use tendermint::block::signed_header::SignedHeader as TMCommit;
use tendermint::block::Header as TMHeader;
use tendermint::block::Height;
use tendermint::lite::TrustThresholdFraction;
use tendermint_rpc::Client as RpcClient;

use core::future::Future;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use crate::client::rpc_requester::RpcRequester;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

use super::Chain;

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: RpcClient,
    requester: RpcRequester,
}

impl CosmosSDKChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, Error> {
        // TODO: Derive Clone on RpcClient in tendermint-rs
        let requester = RpcRequester::new(RpcClient::new(config.rpc_addr.clone()));
        let rpc_client = RpcClient::new(config.rpc_addr.clone());

        Ok(Self {
            config,
            rpc_client,
            requester,
        })
    }
}

impl Chain for CosmosSDKChain {
    type Header = TMHeader;
    type Commit = TMCommit;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;
    type Requester = RpcRequester;
    type Error = anomaly::Error<Kind>;

    fn query(&self, data: Path, height: u64, prove: bool) -> Result<Vec<u8>, Self::Error> {
        let path = TendermintABCIPath::from_str(IBC_QUERY_PATH).unwrap();
        if !data.is_provable() & prove {
            return Err(Kind::Store
                .context("requested proof for a path in the privateStore")
                .into());
        }
        let response = block_on(abci_query(&self, path, data.to_string(), height, prove))?;

        // Verify response proof, if requested.
        if prove {
            dbg!("Todo: implement proof verification."); // Todo: Verify proof
        }

        Ok(response)
    }

    /// Send a transaction that includes the specified messages
    fn send(&self, _msgs: &[Any]) -> Result<(), Error> {
        // TODO sign and broadcast_tx
        Ok(())
    }

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &RpcClient {
        &self.rpc_client
    }

    fn requester(&self) -> &Self::Requester {
        &self.requester
    }

    fn trusting_period(&self) -> Duration {
        self.config.trusting_period
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3)
    }

    fn trust_threshold(&self) -> TrustThresholdFraction {
        TrustThresholdFraction::default()
    }

    fn sign_tx(&self, _msgs: &[Any]) -> Result<Vec<u8>, Error> {
        unimplemented!()

        // TODO: Once the tendermint is upgraded and crypto can be imported then work on this build and signing code
        // This is a pregenerated private key from running:
        //      let signing_key = SigningKey::random(&mut OsRng);
        //      println!("{:?", hex::encode(signing_key.to_bytes()));
        // It corresponds to the address: cosmos14kl05amnc3mdyj5d2r27agvwhuqgz7vwfz0wwj
        // Add it to your genesis or send coins to it.
        // Then query the account number and update account_number here.
        // let signing_key_bytes = "cda4e48a1ae228656e483b2f3ae7bca6d04abcef64189ff56d481987259dd2a4";
        // let account_number = 12;
        //
        // let signing_key = SigningKey::new(&hex::decode(signing_key_bytes).unwrap()).unwrap();
        // let verify_key = VerifyKey::from(&signing_key);
        // let pubkey_bytes = verify_key.to_bytes().to_vec();
        // let addr = get_account(pubkey_bytes.clone());
        // msg.signer = addr; // XXX: replace signer
        //
        // // Build and sign transaction
        // //let _signed = chain.build_sign_tx(vec![Box::new(msg)]);
        //
        // let mut proto_msgs: Vec<prost_types::Any> = Vec::new();
        // let mut buf = Vec::new();
        //
        // // Have a loop if new_builder takes more messages
        // // for now just encode one message
        // prost::Message::encode(&msg, &mut buf).unwrap();
        //
        // // Create a proto any message
        // let any_msg = prost_types::Any {
        //     type_url: "/ibc.connection.MsgConnectionOpenInit".to_string(), // "type.googleapis.com/ibc.connection.MsgConnectionOpenInit".to_string(),
        //     value: buf,
        // };
        //
        // // Add proto message
        // proto_msgs.push(any_msg);
        //
        // // Create TxBody
        // let body = TxBody {
        //     messages: proto_msgs,
        //     memo: "".to_string(),
        //     timeout_height: 0,
        //     extension_options: Vec::<prost_types::Any>::new(),
        //     non_critical_extension_options: Vec::<prost_types::Any>::new(),
        // };
        //
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
        // // A protobuf serialization of a TxBody
        // let mut body_buf = Vec::new();
        // prost::Message::encode(&body, &mut body_buf).unwrap();
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

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
async fn abci_query(
    chain: &CosmosSDKChain,
    path: TendermintABCIPath,
    data: String,
    height: u64,
    prove: bool,
) -> Result<Vec<u8>, anomaly::Error<Kind>> {
    // Use the Tendermint-rs RPC client to do the query.
    let response = chain
        .rpc_client()
        .abci_query(
            Some(path),
            data.into_bytes(),
            match height {
                0 => None,
                _ => Some(Height::from(height)),
            },
            prove,
        )
        .await
        .map_err(|e| Kind::Rpc.context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        return Err(Kind::Rpc.context(response.log.to_string()).into());
    }
    if response.value.is_empty() {
        // Fail due to empty response value (nothing to decode).
        return Err(Kind::EmptyResponseValue.into());
    }

    Ok(response.value)
}

/// block on future
pub fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
