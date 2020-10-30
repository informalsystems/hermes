use std::str::FromStr;
use std::time::Duration;

use bytes::Bytes;
use prost::Message;
use prost_types::Any;
use tendermint::abci::{Path as TendermintABCIPath, Transaction};

use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::validator::Info;
use tendermint_light_client::types::{LightBlock, ValidatorSet};
use tendermint_light_client::types::{SignedHeader, TrustThreshold};
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use super::Chain;
use crate::client::tendermint::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

use crate::error;
use crate::keyring::store::{KeyEntry, KeyRing, KeyRingOperations, StoreBackend};

use crate::util::block_on;

use ibc::ics02_client::client_def::AnyClientState;
use ibc::ics24_host::identifier::ClientId;
use ibc::tx_msg::Msg;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
use k256::ecdsa::{SigningKey, VerifyKey};
use std::convert::TryInto;
use tendermint::consensus::Params;
use tendermint::vote::Power;

use bitcoin::hashes::hex::ToHex;
use tendermint_proto::DomainType;

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    light_client: Option<LightClient>,
    pub keybase: KeyRing,
}

impl CosmosSDKChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, Error> {
        let rpc_client =
            HttpClient::new(config.rpc_addr.clone()).map_err(|e| Kind::Rpc.context(e))?;

        let key_store = KeyRing::init(StoreBackend::Memory);

        Ok(Self {
            config,
            keybase: key_store,
            rpc_client,
            light_client: None,
        })
    }

    /// Query the consensus parameters via an RPC query
    /// Specific to the SDK and used only for Tendermint client create
    pub fn query_consensus_params(&self) -> Result<Params, Error> {
        Ok(block_on(self.rpc_client().genesis())
            .map_err(|e| error::Kind::Rpc.context(e))?
            .consensus_params)
    }

    /// Get the key and account Id - temporary solution
    pub fn key_and_signer(&mut self, seed_file_name: &str) -> Result<(KeyEntry, AccountId), Error> {
        // Get the key from key seed file
        let key = self
            .keybase
            .key_from_seed_file(seed_file_name)
            .map_err(|e| Kind::KeyBase.context(e))?;

        let signer: AccountId =
            AccountId::from_str(&key.address.to_hex()).map_err(|e| Kind::KeyBase.context(e))?;

        Ok((key, signer))
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
        acct_seq: u64,
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

        let single = Single { mode: 1 };
        let sum_single = Some(Sum::Single(single));
        let mode = Some(ModeInfo { sum: sum_single });
        let signer_info = SignerInfo {
            public_key: Some(pk_any),
            mode_info: mode,
            sequence: acct_seq,
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

    fn trusting_period(&self) -> Duration {
        self.config.trusting_period
    }

    fn trust_threshold(&self) -> TrustThreshold {
        TrustThreshold::default()
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3 * 3600)
    }

    fn query_header_at_height(&self, height: Height) -> Result<LightBlock, Error> {
        let client = self.rpc_client();

        let signed_header = fetch_signed_header(client, height)?;
        assert_eq!(height, signed_header.header().height);

        // Get the validator list
        let validators = fetch_validators(client, height)?;

        // Get the proposer
        let proposer = validators
            .iter()
            .find(|v| v.address == signed_header.header().proposer_address)
            .ok_or_else(|| Kind::EmptyResponseValue)?;

        let voting_power: u64 = validators.iter().map(|v| v.voting_power.value()).sum();

        // Create the validator set with the proposer from the header
        // This is required by IBC on-chain validation
        let validator_set = ValidatorSet::new(
            validators.clone(),
            Some(*proposer),
            // 0_u64.try_into().unwrap(), // TODO - iterate and add voting powers
            voting_power.try_into().unwrap(), // TODO - iterate and add voting powers
        );

        // Create the next validator set without the proposer
        let next_validator_set = fetch_validator_set(client, height.increment())?;

        let light_block = LightBlock::new(
            signed_header,
            validator_set,
            next_validator_set,
            self.config().peer_id,
        );

        Ok(light_block)
    }

    fn query_client_state(&self, client_id: &ClientId) -> Result<AnyClientState, Error> {
        Ok(self
            .query(
                ClientStatePath(client_id.clone()),
                0_u64
                    .try_into()
                    .map_err(|e| Kind::BadParameter.context(e))?,
                false,
            )
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| AnyClientState::decode_vec(&v).map_err(|e| Kind::Query.context(e)))
            .map_err(|_| Kind::Query)?)
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
        .broadcast_tx_sync(Transaction::from(data))
        .await
        .map_err(|e| Kind::Rpc.context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        println!("Tx Error Response: {:?}", response);
        return Err(Kind::Rpc.context(response.log.to_string()).into());
    }

    Ok(response.data.as_bytes().to_vec())
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
        Ok(response) => Ok(ValidatorSet::new(
            response.validators.clone(),
            Some(response.validators[0]),
            0_u64.try_into().unwrap(),
        )),
        Err(err) => Err(Kind::Rpc.context(err).into()),
    }
}

fn fetch_validators(client: &HttpClient, height: Height) -> Result<Vec<Info>, Error> {
    let res = block_on(client.validators(height));

    match res {
        Ok(response) => Ok(response.validators),
        Err(err) => Err(Kind::Rpc.context(err).into()),
    }
}
