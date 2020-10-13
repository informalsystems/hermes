use std::str::FromStr;
use std::time::Duration;

use tendermint::abci::{Path as TendermintABCIPath, Transaction};
use tendermint::block::Height;
use tendermint_light_client::types::LightBlock;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use super::Chain;
use crate::client::tendermint::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

use bytes::Bytes;
use ibc_proto::cosmos::base::crypto::v1beta1::public_key::Sum as PKSum;
use ibc_proto::cosmos::base::crypto::v1beta1::PublicKey as RawPublicKey;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, ModeInfo, SignDoc, SignerInfo, TxBody};
use k256::ecdsa::{SigningKey, VerifyKey};
use prost::Message;
use prost_types::Any;
use std::future::Future;

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
    fn send(&self, msgs: &[Any], memo: String, timeout_height: u64) -> Result<(), Error> {
        // Create TxBody
        let body = TxBody {
            messages: msgs.to_vec(),
            memo,
            timeout_height,
            extension_options: Vec::<Any>::new(),
            non_critical_extension_options: Vec::<Any>::new(),
        };

        // A protobuf serialization of a TxBody
        let mut body_buf = Vec::new();
        prost::Message::encode(&body, &mut body_buf).unwrap();

        let signing_key_bytes = "cda4e48a1ae228656e483b2f3ae7bca6d04abcef64189ff56d481987259dd2a4";
        let account_number = 8;

        let signing_key = SigningKey::new(&hex::decode(signing_key_bytes).unwrap()).unwrap();
        let verify_key = VerifyKey::from(&signing_key);
        let pubkey_bytes = verify_key.to_bytes().to_vec();

        let sum = Some(PKSum::Secp256k1(pubkey_bytes));
        let pk = RawPublicKey { sum };
        let single = Single { mode: 1 };
        let sum_single = Some(Sum::Single(single));
        let mode = Some(ModeInfo { sum: sum_single });

        // A protobuf serialization of a Public Key
        let mut pk_buf = Vec::new();
        prost::Message::encode(&pk, &mut pk_buf).unwrap();

        // Create a MsgSend proto Any message
        let pk_any = Any {
            type_url: "/cosmos.base.crypto.v1beta1.PublicKey.".to_string(),
            value: pk_buf,
        };

        let signer_info = SignerInfo {
            public_key: Some(pk_any),
            mode_info: mode,
            sequence: 0,
        };

        let auth_info = AuthInfo {
            signer_infos: vec![signer_info],
            fee: None,
        };

        // A protobuf serialization of a AuthInfo
        let mut auth_buf = Vec::new();
        prost::Message::encode(&auth_info, &mut auth_buf).unwrap();

        let sign_doc = SignDoc {
            body_bytes: body_buf.clone(),
            auth_info_bytes: auth_buf.clone(),
            chain_id: self.config.clone().id.to_string(),
            account_number,
        };

        //TODO: sign doc and broadcast

        //let signed = sign(sign_doc);
        //broadcast_tx(self, )

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

    fn trusting_period(&self) -> Duration {
        self.config.trusting_period
    }

    fn trust_threshold(&self) -> TrustThreshold {
        TrustThreshold::default()
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3)
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
        return Err(Kind::Rpc.context(response.log.to_string()).into());
    }
    if response.data.as_bytes().len() == 0 {
        // Fail due to empty response value (nothing to decode).
        return Err(Kind::EmptyResponseValue.into());
    }

    Ok(response.data.as_bytes().to_vec())
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
