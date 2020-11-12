use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use std::time::Duration;

use anomaly::fail;
use bytes::Bytes;
use prost::Message;
use prost_types::Any;

use bitcoin::hashes::hex::ToHex;
use k256::ecdsa::{SigningKey, VerifyKey};

use tendermint_proto::crypto::ProofOps;
use tendermint_proto::DomainType;
use tendermint_rpc::endpoint::abci_query::AbciQuery;
use tendermint_rpc::endpoint::broadcast;

use tendermint::abci::{Path as TendermintABCIPath, Transaction};
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::consensus::Params;
use tendermint::validator::Info;
use tendermint::vote::Power;
use tendermint_light_client::types::{
    LightBlock as TMLightBlock, SignedHeader, TrustThreshold, ValidatorSet,
};
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

// Support for GRPC
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::staking::v1beta1::Params as StakingParams;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
use tonic::codegen::http::Uri;

use ibc::downcast;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty};
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics07_tendermint::header::Header as TMHeader;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics23_commitment::merkle::MerkleProof;
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::ics24_host::Path::ClientConsensusState as ClientConsensusPath;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;

use super::Chain;

use crate::chain::QueryResponse;
use crate::config::ChainConfig;
use crate::error::{self, Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing, KeyRingOperations, StoreBackend};
use crate::light_client::tendermint::LightClient;
use crate::util::block_on;

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

    /// The unbonding period of this chain
    pub fn unbonding_period(&self) -> Result<Duration, Error> {
        // TODO - generalize this
        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;

        let mut client = block_on(
            ibc_proto::cosmos::staking::v1beta1::query_client::QueryClient::connect(grpc_addr),
        )
        .map_err(|e| Kind::Grpc.context(e))?;

        let request =
            tonic::Request::new(ibc_proto::cosmos::staking::v1beta1::QueryParamsRequest {});

        let response = block_on(client.params(request)).map_err(|e| Kind::Grpc.context(e))?;

        let res = response
            .into_inner()
            .params
            .ok_or_else(|| Kind::Grpc.context("none staking params".to_string()))?
            .unbonding_time
            .ok_or_else(|| Kind::Grpc.context("none unbonding time".to_string()))?;

        Ok(Duration::from_secs(res.seconds as u64))
    }

    /// Query the consensus parameters via an RPC query
    /// Specific to the SDK and used only for Tendermint client create
    pub fn query_consensus_params(&self) -> Result<Params, Error> {
        Ok(block_on(self.rpc_client().genesis())
            .map_err(|e| Kind::Rpc.context(e))?
            .consensus_params)
    }
}

impl Chain for CosmosSDKChain {
    type Header = TMHeader;
    type LightBlock = TMLightBlock;
    type RpcClient = HttpClient;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &HttpClient {
        &self.rpc_client
    }

    fn query(&self, data: Path, height: ICSHeight, prove: bool) -> Result<QueryResponse, Error> {
        let path = TendermintABCIPath::from_str(IBC_QUERY_PATH).unwrap();

        let height =
            Height::try_from(height.version_height).map_err(|e| Kind::InvalidHeight.context(e))?;

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
    /// TODO - split the messages in multiple Tx-es such that they don't exceed some max size
    fn send(
        &mut self,
        proto_msgs: Vec<Any>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<String, Error> {
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
            gas_limit: 150000,
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

        let response =
            block_on(broadcast_tx_commit(self, txraw_buf)).map_err(|e| Kind::Rpc.context(e))?;

        Ok(response)
    }

    /// Get the key and account Id - temporary solution
    fn key_and_signer(&mut self, key_file_contents: &str) -> Result<(KeyEntry, AccountId), Error> {
        // Get the key from key seed file
        let key = self
            .keybase
            .key_from_seed_file(key_file_contents)
            .map_err(|e| Kind::KeyBase.context(e))?;

        let signer: AccountId =
            AccountId::from_str(&key.address.to_hex()).map_err(|e| Kind::KeyBase.context(e))?;

        Ok((key, signer))
    }

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<ICSHeight, Error> {
        let status = block_on(self.rpc_client().status()).map_err(|e| Kind::Rpc.context(e))?;

        if status.sync_info.catching_up {
            fail!(
                Kind::LightClient,
                "node at {} running chain {} not caught up",
                self.config().rpc_addr,
                self.config().id,
            );
        }

        Ok(ICSHeight {
            version_number: ChainId::chain_version(status.node_info.network.as_str()),
            version_height: u64::from(status.sync_info.latest_block_height),
        })
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<Self::ClientState, Error> {
        Ok(self
            .query(ClientStatePath(client_id.clone()), height, false)
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| {
                Self::ClientState::decode_vec(&v.value).map_err(|e| Kind::Query.context(e))
            })?)
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        let res = self
            .query(ClientStatePath(client_id.clone()), height, true)
            .map_err(|e| Kind::Query.context(e))?;

        let state =
            Self::ClientState::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        Ok((state, res.proof))
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: ICSHeight,
        height: ICSHeight,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        let res = self
            .query(
                ClientConsensusPath {
                    client_id: client_id.clone(),
                    epoch: consensus_height.version_number,
                    height: consensus_height.version_height,
                },
                height,
                true,
            )
            .map_err(|e| Kind::Query.context(e))?;

        let consensus_state =
            Self::ConsensusState::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        Ok((consensus_state, res.proof))
    }

    fn build_client_state(&self, height: ICSHeight) -> Result<Self::ClientState, Error> {
        // Build the client state.
        let client_state = ibc::ics07_tendermint::client_state::ClientState::new(
            self.id().to_string(),
            self.config.trust_threshold,
            self.config.trusting_period,
            self.unbonding_period()?,
            Duration::from_millis(3000), // TODO - get it from src config when avail
            height,
            ICSHeight::zero(),
            self.query_consensus_params()?,
            "upgrade/upgradedClient".to_string(),
            false,
            false,
        )
        .map_err(|e| Kind::BuildClientStateFailure.context(e))?;

        Ok(client_state)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        Ok(TMConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &self,
        trusted_light_block: Self::LightBlock,
        target_light_block: Self::LightBlock,
    ) -> Result<Self::Header, Error> {
        let trusted_height =
            ICSHeight::new(self.id().version(), trusted_light_block.height().into());

        Ok(TMHeader {
            trusted_height,
            signed_header: target_light_block.signed_header,
            validator_set: target_light_block.validators,
            trusted_validator_set: trusted_light_block.validators,
        })
    }

    fn downcast_header(&self, header: AnyHeader) -> Option<Self::Header> {
        downcast!(header => AnyHeader::Tendermint)
    }

    fn downcast_client_state(&self, client_state: AnyClientState) -> Option<ClientState> {
        downcast!(client_state => AnyClientState::Tendermint)
    }

    fn downcast_consensus_state(
        &self,
        consensus_state: AnyConsensusState,
    ) -> Option<Self::ConsensusState> {
        downcast!(consensus_state => AnyConsensusState::Tendermint)
    }
}

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
async fn abci_query(
    chain: &CosmosSDKChain,
    path: TendermintABCIPath,
    data: String,
    height: Height,
    prove: bool,
) -> Result<QueryResponse, anomaly::Error<Kind>> {
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
    if prove && response.proof.is_none() {
        // Fail due to empty proof
        return Err(Kind::EmptyResponseProof.into());
    }

    let raw_proof_ops = response
        .proof
        .map(ProofOps::try_from)
        .transpose()
        .map_err(|e| Kind::MalformedProof.context(e))?;

    let response = QueryResponse {
        value: response.value,
        proof: MerkleProof {
            proof: raw_proof_ops,
        },
        height: response.height,
    };

    Ok(response)
}

/// Perform a `broadcast_tx_sync`, and return the corresponding deserialized response data.
async fn broadcast_tx_sync(
    chain: &CosmosSDKChain,
    data: Vec<u8>,
) -> Result<String, anomaly::Error<Kind>> {
    let response = chain
        .rpc_client()
        .broadcast_tx_sync(data.into())
        .await
        .map_err(|e| Kind::Rpc.context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        println!("Tx Error Response: {:?}", response);
        return Err(Kind::Rpc.context(response.log.to_string()).into());
    }

    Ok(serde_json::to_string_pretty(&response).unwrap())
}

/// Perform a `broadcast_tx_commit`, and return the corresponding deserialized response data.
/// TODO - move send() to this once RPC tendermint response is fixed
async fn broadcast_tx_commit(
    chain: &CosmosSDKChain,
    data: Vec<u8>,
) -> Result<String, anomaly::Error<Kind>> {
    let response = chain
        .rpc_client()
        .broadcast_tx_commit(data.into())
        .await
        .map_err(|e| Kind::Rpc.context(e))?;

    Ok(serde_json::to_string(&response).unwrap())
}

fn fetch_signed_header(client: &HttpClient, height: Height) -> Result<SignedHeader, Error> {
    Ok(block_on(client.commit(height))
        .map_err(|e| Kind::Rpc.context(e))?
        .signed_header)
}

fn fetch_validators(client: &HttpClient, height: Height) -> Result<Vec<Info>, Error> {
    Ok(block_on(client.validators(height))
        .map_err(|e| Kind::Rpc.context(e))?
        .validators)
}

fn fetch_validator_set(client: &HttpClient, height: Height) -> Result<ValidatorSet, Error> {
    Ok(ValidatorSet::new_simple(fetch_validators(client, height)?))
}

/// Uses the GRPC client to retrieve the account sequence
async fn query_account(chain: &mut CosmosSDKChain, address: String) -> Result<BaseAccount, Error> {
    let grpc_addr = Uri::from_str(&chain.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
    let mut client =
        ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient::connect(grpc_addr)
            .await
            .map_err(|e| Kind::Grpc.context(e))?;

    let request = tonic::Request::new(QueryAccountRequest { address });

    let response = client.account(request).await;

    let base_account = BaseAccount::decode(
        response
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner()
            .account
            .unwrap()
            .value
            .as_slice(),
    )
    .map_err(|e| Kind::Grpc.context(e))?;

    Ok(base_account)
}
