use std::future::Future;
use std::str::FromStr;
use std::time::Duration;

use bytes::Bytes;
use prost::Message;
use prost_types::Any;

use tendermint::abci::Path as TendermintABCIPath;
use tendermint::block::Height;
use tendermint_light_client::types::{LightBlock, ValidatorSet};
use tendermint_light_client::types::{SignedHeader, TrustThreshold};
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use super::Chain;
use crate::client::tendermint::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::util::block_on;

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    light_client: Option<LightClient>,
}

impl CosmosSDKChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, Error> {
        let rpc_client =
            HttpClient::new(config.rpc_addr.clone()).map_err(|e| Kind::Rpc.context(e))?;

        Ok(Self {
            config,
            rpc_client,
            light_client: None,
        })
    }
}

impl Chain for CosmosSDKChain {
    type LightBlock = LightBlock;
    type LightClient = LightClient;
    type RpcClient = HttpClient;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;
    type Error = Error;

    fn query(&self, data: Path, height: Height, prove: bool) -> Result<Vec<u8>, Self::Error> {
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

    fn rpc_client(&self) -> &HttpClient {
        &self.rpc_client
    }

    fn set_light_client(&mut self, light_client: LightClient) {
        self.light_client = Some(light_client);
    }

    fn light_client(&self) -> Option<&LightClient> {
        self.light_client.as_ref()
    }

    fn trust_threshold(&self) -> TrustThreshold {
        TrustThreshold::default()
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3)
    }

    fn query_header_at_height(&self, height: Height) -> Result<LightBlock, Error> {
        let client = self.rpc_client();

        let signed_header = fetch_signed_header(client, height)?;
        assert_eq!(height, signed_header.header.height);

        let validator_set = fetch_validator_set(client, height)?;
        let next_validator_set = fetch_validator_set(client, height.increment())?;

        let light_block = LightBlock::new(
            signed_header,
            validator_set,
            next_validator_set,
            self.config().peer_id,
        );

        Ok(light_block)
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
    height: Height,
    prove: bool,
) -> Result<Vec<u8>, anomaly::Error<Kind>> {
    let height = if height.value() == 0 {
        None
    } else {
        Some(height)
    };

    // Use the Tendermint-rs RPC client to do the query.
    let response = chain
        .rpc_client()
        .abci_query(Some(path), data.into_bytes(), height, prove)
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

fn fetch_signed_header(client: &HttpClient, height: Height) -> Result<SignedHeader, Error> {
    let res = block_on(client.commit(height));

    match res {
        Ok(response) => Ok(response.signed_header),
        Err(err) => Err(Kind::Rpc.context(err).into()),
    }
}

fn fetch_validator_set(client: &HttpClient, height: Height) -> Result<ValidatorSet, Error> {
    let res = block_on(client.validators(height));

    match res {
        Ok(response) => Ok(ValidatorSet::new(response.validators)),
        Err(err) => Err(Kind::Rpc.context(err).into()),
    }
}
