use std::str::FromStr;
use std::time::Duration;

use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};
use tendermint::abci::{Path as TendermintABCIPath, Transaction};
use tendermint::block::Height;
use tendermint_light_client::types::{LightBlock, ValidatorSet};
use tendermint_light_client::types::{SignedHeader, TrustThreshold};
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use super::Chain;
use crate::client::tendermint::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::util::block_on;

use crate::error;
use crate::keyring::store::{KeyEntry, KeyRing, KeyRingOperations, StoreBackend};
use bytes::Bytes;
use futures::{FutureExt, TryFutureExt};
use ibc::tx_msg::Msg;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
use k256::ecdsa::{SigningKey, VerifyKey};
use prost::Message;
use prost_types::Any;
use std::future::Future;

// Support for GRPC
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use tonic::codegen::http::Uri;

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    light_client: Option<LightClient>,
    pub keybase: KeyRing,
}

impl CosmosSDKChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, Error> {
        let primary = config
            .primary()
            .ok_or_else(|| Kind::LightClient.context("no primary peer specified"))?;

        let rpc_client =
            HttpClient::new(primary.address.clone()).map_err(|e| Kind::Rpc.context(e))?;

        let key_store = KeyRing::init(StoreBackend::Memory);

        Ok(Self {
            config,
            keybase: key_store,
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
    fn send(
        &mut self,
        msg_type: String,
        msg_bytes: Vec<u8>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<Vec<u8>, Error> {
        // Create a proto any message
        let mut proto_msgs: Vec<Any> = Vec::new();

        let any_msg = Any {
            type_url: msg_type,
            value: msg_bytes,
        };

        // Add proto message
        proto_msgs.push(any_msg);

        // Create TxBody
        let body = TxBody {
            messages: proto_msgs.to_vec(),
            memo,
            timeout_height,
            extension_options: Vec::<Any>::new(),
            non_critical_extension_options: Vec::<Any>::new(),
        };

        // A protobuf serialization of a TxBody
        let mut body_buf = Vec::new();
        prost::Message::encode(&body, &mut body_buf).unwrap();

        // let key = self.keybase.get(signer.clone()).map_err(|e| error::Kind::KeyBase.context(e))?;
        let pub_key_bytes = key.public_key.public_key.to_bytes();

        let mut pk_buf = Vec::new();
        prost::Message::encode(&key.public_key.public_key.to_bytes(), &mut pk_buf).unwrap();

        // Create a MsgSend proto Any message
        let pk_any = Any {
            type_url: "/cosmos.crypto.secp256k1.PubKey".to_string(),
            value: pk_buf,
        };

        let acct_response =
            block_on(query_account(self, key.account)).map_err(|e| Kind::Grpc.context(e))?;

        let single = Single { mode: 1 };
        let sum_single = Some(Sum::Single(single));
        let mode = Some(ModeInfo { sum: sum_single });
        let signer_info = SignerInfo {
            public_key: Some(pk_any),
            mode_info: mode,
            sequence: acct_response.sequence,
        };

        // Gas Fee
        let coin = Coin {
            denom: "stake".to_string(),
            amount: "1000".to_string(),
        };

        let fee = Some(Fee {
            amount: vec![coin],
            gas_limit: 100000,
            payer: "".to_string(),
            granter: "".to_string(),
        });

        let auth_info = AuthInfo {
            signer_infos: vec![signer_info],
            fee,
        };

        // A protobuf serialization of a AuthInfo
        let mut auth_buf = Vec::new();
        prost::Message::encode(&auth_info, &mut auth_buf).unwrap();

        let sign_doc = SignDoc {
            body_bytes: body_buf.clone(),
            auth_info_bytes: auth_buf.clone(),
            chain_id: self.config.clone().id.to_string(),
            account_number: 0,
        };

        // A protobuf serialization of a SignDoc
        let mut signdoc_buf = Vec::new();
        prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

        // Sign doc and broadcast
        let signed = self.keybase.sign(key.address, signdoc_buf);

        let tx_raw = TxRaw {
            body_bytes: body_buf,
            auth_info_bytes: auth_buf,
            signatures: vec![signed],
        };

        let mut txraw_buf = Vec::new();
        prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();
        //println!("TxRAW {:?}", hex::encode(txraw_buf.clone()));

        //let signed = sign(sign_doc);
        let response = block_on(broadcast_tx(self, txraw_buf)).map_err(|e| Kind::Rpc.context(e))?;

        Ok(response)
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
        let primary = self
            .config()
            .primary()
            .ok_or_else(|| Kind::LightClient.context("no primary peer configured"))?;

        let signed_header = fetch_signed_header(client, height)?;
        assert_eq!(height, signed_header.header.height);

        let validator_set = fetch_validator_set(client, height)?;
        let next_validator_set = fetch_validator_set(client, height.increment())?;

        let light_block = LightBlock::new(
            signed_header,
            validator_set,
            next_validator_set,
            primary.peer_id,
        );

        Ok(light_block)
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

/// Perform a generic `broadcast_tx`, and return the corresponding deserialized response data.
async fn broadcast_tx(
    chain: &CosmosSDKChain,
    data: Vec<u8>,
) -> Result<Vec<u8>, anomaly::Error<Kind>> {
    // Use the Tendermint-rs RPC client to do the query.
    let response = chain
        .rpc_client()
        .broadcast_tx_sync(Transaction::new(data))
        .await
        .map_err(|e| Kind::Rpc.context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        println!("Tx Error Response: {:?}", response);
        return Err(Kind::Rpc.context(response.log.to_string()).into());
    }

    Ok(response.data.as_bytes().to_vec())
}

fn fetch_validator_set(client: &HttpClient, height: Height) -> Result<ValidatorSet, Error> {
    let res = block_on(client.validators(height));

    match res {
        Ok(response) => Ok(ValidatorSet::new(response.validators)),
        Err(err) => Err(Kind::Rpc.context(err).into()),
    }
}

/// Uses the GRPC client to retrieve the account sequence
async fn query_account(chain: &mut CosmosSDKChain, address: String) -> Result<BaseAccount, Error> {
    let grpc_addr = Uri::from_str(&chain.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
    let mut client = QueryClient::connect(grpc_addr)
        .await
        .map_err(|e| Kind::Grpc.context(e))?;

    let request = tonic::Request::new(QueryAccountRequest { address });

    let response = client.account(request).await;

    let base_account: BaseAccount = BaseAccount::decode(
        response
            .unwrap()
            .into_inner()
            .account
            .unwrap()
            .value
            .as_slice(),
    )
    .map_err(|e| Kind::Grpc.context(e))?;

    Ok(base_account)
}
