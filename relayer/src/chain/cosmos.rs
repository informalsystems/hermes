use anomaly::fail;
use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use std::time::Duration;

use bytes::Bytes;
use prost::Message;
use prost_types::Any;

use bitcoin::hashes::hex::ToHex;
use k256::ecdsa::{SigningKey, VerifyKey};

use tendermint_proto::DomainType;

use tendermint::abci::{Path as TendermintABCIPath, Transaction};
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::consensus::Params;
use tendermint::validator::Info;
use tendermint::vote::Power;
use tendermint_light_client::types::{LightBlock, SignedHeader, TrustThreshold, ValidatorSet};
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::msgs::{MsgCreateAnyClient, MsgUpdateAnyClient};
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::ics24_host::Path::ClientState as ClientStatePath;

use ibc::ics24_host::{Path, IBC_QUERY_PATH};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};

use super::Chain;
use crate::client::tendermint::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing, KeyRingOperations, StoreBackend};
use crate::tx::connection::ConnectionOpenInitOptions;
use crate::util::block_on;
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty};
use ibc::ics04_channel::msgs::MsgChannelOpenInit;
use ibc_proto::ibc::core::connection::v1::ConnectionPaths;

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
            .map_err(|e| Kind::Rpc.context(e))?
            .consensus_params)
    }

    /// Get the key and account Id - temporary solution
    pub fn key_and_signer(&mut self, signer_file: &str) -> Result<(KeyEntry, AccountId), Error> {
        // Get the key from key seed file
        let key = self
            .keybase
            .key_from_seed_file(signer_file)
            .map_err(|e| Kind::KeyBase.context(e))?;

        let signer: AccountId =
            AccountId::from_str(&key.address.to_hex()).map_err(|e| Kind::KeyBase.context(e))?;

        Ok((key, signer))
    }

    /// Query the latest header via RPC
    fn query_latest_light_block(&self) -> Result<LightBlock, Error> {
        let height = self.query_latest_height()?;
        self.query_light_block_at_height(height)
    }

    fn query_light_block_at_height(&self, height: Height) -> Result<LightBlock, Error> {
        let client = self.rpc_client();

        let signed_header = fetch_signed_header(client, height)?;
        assert_eq!(height, signed_header.header().height);

        // Get the validator list.
        let validators = fetch_validators(client, height)?;

        // Get the proposer.
        let proposer = validators
            .iter()
            .find(|v| v.address == signed_header.header().proposer_address)
            .ok_or_else(|| Kind::EmptyResponseValue)?;

        let voting_power: u64 = validators.iter().map(|v| v.voting_power.value()).sum();

        // Create the validator set with the proposer from the header.
        // This is required by IBC on-chain validation.
        let validator_set = ValidatorSet::new(
            validators.clone(),
            Some(*proposer),
            voting_power.try_into().map_err(|e| Kind::Rpc.context(e))?,
        );

        // Create the next validator set without the proposer.
        let next_validator_set = fetch_validator_set(client, height.increment())?;

        let light_block = LightBlock::new(
            signed_header,
            validator_set,
            next_validator_set,
            self.config().peer_id,
        );

        Ok(light_block)
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
        proto_msgs: Vec<Any>,
        key: KeyEntry,
        acct_seq: u64,
        memo: String,
        timeout_height: u64,
    ) -> Result<Vec<u8>, Error> {
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
        // TODO - get it from src config when avail
        // TODO - Should this be part of the Chain trait?
        TrustThreshold {
            numerator: 1,
            denominator: 3,
        }
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3 * 3600)
    }

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<Height, Error> {
        let status = block_on(self.rpc_client().status()).map_err(|e| Kind::Rpc.context(e))?;

        if status.sync_info.catching_up {
            fail!(
                Kind::LightClient,
                "node at {} running chain {} not caught up",
                self.config().rpc_addr,
                self.config().id,
            );
        }

        Ok(status.sync_info.latest_block_height)
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
        proof: bool,
    ) -> Result<AnyClientState, Error> {
        Ok(self
            .query(ClientStatePath(client_id.clone()), height, proof)
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| AnyClientState::decode_vec(&v).map_err(|e| Kind::Query.context(e)))?)
    }

    fn build_create_client_msg(
        &self,
        client_id: ClientId,
        signer: AccountId,
    ) -> Result<MsgCreateAnyClient, Error> {
        // Get the latest header from the source chain and build the consensus state.
        let latest_light_block = self.query_latest_light_block()?;
        let consensus_params = self.query_consensus_params()?;

        // Build the consensus state.
        let consensus_state = AnyConsensusState::Tendermint(TendermintConsensusState::from(
            latest_light_block.signed_header.header().clone(),
        ));

        let height = u64::from(latest_light_block.signed_header.header().height);
        let version = latest_light_block
            .signed_header
            .header()
            .chain_id
            .to_string();

        // Build the client state.
        let client_state = ibc::ics07_tendermint::client_state::ClientState::new(
            self.id().to_string(),
            self.trust_threshold(),
            self.trusting_period(),
            self.unbonding_period(),
            Duration::from_millis(3000), // TODO - get it from src config when avail
            ICSHeight::new(ChainId::chain_version(version), height),
            consensus_params,
            ICSHeight::zero(),
            "upgrade/upgradedClient".to_string(),
            false,
            false,
        )
        .map_err(|e| {
            Kind::CreateClient(client_id.clone(), "failed to build the client state".into())
                .context(e)
        })
        .map(AnyClientState::Tendermint)?;

        Ok(
            MsgCreateAnyClient::new(client_id, client_state, consensus_state, signer).map_err(
                |e| {
                    Kind::MessageTransaction("failed to build the create client message".into())
                        .context(e)
                },
            )?,
        )
    }

    fn build_update_client_msg(
        &self,
        client_id: ClientId,
        trusted_height: ICSHeight,
        target_height: Height,
        signer: AccountId,
    ) -> Result<MsgUpdateAnyClient, Error> {
        // Get the light block at target_height from source chain.
        let target_light_block = self.query_light_block_at_height(target_height)?;

        // Get the light block at trusted_height from the source chain.
        let height =
            Height::try_from(trusted_height.version_height).map_err(|e| Kind::Query.context(e))?;
        let trusted_light_block = self.query_light_block_at_height(height)?;

        // Create the ics07 Header to be included in the MsgUpdateClient.
        let header = AnyHeader::Tendermint(TendermintHeader {
            signed_header: target_light_block.signed_header,
            validator_set: target_light_block.validators,
            trusted_height,
            trusted_validator_set: trusted_light_block.validators,
        });

        Ok(MsgUpdateAnyClient::new(client_id, header, signer))
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
        .broadcast_tx_sync(data.into())
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
    Ok(block_on(client.commit(height))
        .map_err(|e| Kind::Rpc.context(e))?
        .signed_header)
}

fn fetch_validator_set(client: &HttpClient, height: Height) -> Result<ValidatorSet, Error> {
    Ok(ValidatorSet::new_simple(fetch_validators(client, height)?))
}

fn fetch_validators(client: &HttpClient, height: Height) -> Result<Vec<Info>, Error> {
    Ok(block_on(client.validators(height))
        .map_err(|e| Kind::Rpc.context(e))?
        .validators)
}
