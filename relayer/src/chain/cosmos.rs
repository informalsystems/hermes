use std::{convert::TryFrom, future::Future, str::FromStr, time::Duration};

use bytes::Bytes;
use futures::{FutureExt, TryFutureExt};
use k256::ecdsa::{SigningKey, VerifyKey};
use prost::Message;
use prost_types::Any;

use ibc::{
    downcast,
    events::IBCEvent,
    ics02_client::{
        client_def::{AnyClientState, AnyHeader},
        header::Header,
    },
    ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit,
    ics04_channel::packet::Packet,
    ics07_tendermint::client_state::ClientState,
    ics07_tendermint::consensus_state::ConsensusState,
    ics24_host::{Path, IBC_QUERY_PATH},
};
use ibc::{ics02_client::client_def::AnyConsensusState, tx_msg::Msg};

use ibc_proto::cosmos::{
    base::v1beta1::Coin,
    tx::v1beta1::{
        mode_info::{Single, Sum},
        AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw,
    },
};

use tendermint::abci::{Path as ABCIPath, Transaction};
use tendermint::block::Height;
use tendermint_light_client::types::{
    LightBlock as TMLightBlock, SignedHeader, TrustThreshold, ValidatorSet,
};
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use super::Chain;
use crate::error;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing, KeyRingOperations, StoreBackend};
use crate::light_client::tendermint::LightClient;
use crate::util::block_on;
use crate::{config::ChainConfig, light_client::LightBlock};

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

    /// Performs a generic abci_query, and returns the response data.
    async fn abci_query(
        &self,
        data: String,
        height: ibc::Height,
        prove: bool,
    ) -> Result<Vec<u8>, Error> {
        let height = Some(height)
            .filter(|h| !h.is_zero())
            .map(|h| Height::try_from(h.version_height).unwrap());

        let path = ABCIPath::from_str(IBC_QUERY_PATH).unwrap();

        // Use the Tendermint-rs RPC client to do the query.
        let response = self
            .rpc_client
            .abci_query(Some(path), data.into_bytes(), height, prove)
            .await
            .map_err(|e| Kind::Rpc.context(e))?;

        if !response.code.is_ok() {
            // Fail with response log.
            return Err(Kind::Rpc.context(response.log.to_string()).into());
        }

        if response.value.is_empty() {
            // Fail due to empty response value (nothing to decode).
            return Err(Kind::Rpc.context("Empty response value".to_string()).into());
        }

        Ok(response.value)
    }
}

impl LightBlock<CosmosSDKChain> for TMLightBlock {
    fn signed_header(&self) -> &SignedHeader {
        &self.signed_header
    }
}

impl Chain for CosmosSDKChain {
    type Header = SignedHeader;
    type LightBlock = TMLightBlock;
    type RpcClient = HttpClient;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;

    fn query(&self, data: Path, height: ibc::Height, prove: bool) -> Result<Vec<u8>, Error> {
        if !data.is_provable() & prove {
            return Err(Kind::Store
                .context("requested proof for a path in the privateStore")
                .into());
        }

        let response = block_on(self.abci_query(data.to_string(), height, prove))?;

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

    fn trust_threshold(&self) -> TrustThreshold {
        TrustThreshold::default()
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3)
    }

    fn query_header_at_height(&self, height: Height) -> Result<SignedHeader, Error> {
        let client = self.rpc_client();
        let primary = self
            .config()
            .primary()
            .ok_or_else(|| Kind::LightClient.context("no primary peer configured"))?;

        let signed_header = fetch_signed_header(client, height)?;
        assert_eq!(height, signed_header.header.height);

        Ok(signed_header)
    }

    fn create_packet(&self, _event: IBCEvent) -> Result<Packet, Error> {
        todo!()
    }

    fn assemble_client_state(&self, header: &SignedHeader) -> Result<Self::ClientState, Error> {
        // Downcast from the generic any header into a header specific for this type of chain.
        let height = u64::from(header.header.height);

        // Build the client state.
        let client_state = ClientState::new(
            self.id().to_string(), // The id of this chain.
            self.config.trusting_period,
            self.unbonding_period(),
            Duration::from_millis(3000),
            ibc::Height::new(self.id().version(), height),
            ibc::Height::new(self.id().version(), 0),
            "".to_string(),
            false,
            false,
        )
        .map_err(|e| Kind::Ics007.context(e))?;

        Ok(client_state)
    }

    fn assemble_consensus_state(&self, header: &SignedHeader) -> Result<ConsensusState, Error> {
        Ok(ConsensusState::from(header.clone()))
    }

    fn downcast_header(&self, header: AnyHeader) -> Option<SignedHeader> {
        downcast!(header => AnyHeader::Tendermint).map(|h| h.signed_header)
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
