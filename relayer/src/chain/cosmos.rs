
use std::{
    convert::TryFrom,
    future::Future,
    str::FromStr,
    sync::{Arc, Mutex},
    thread,
    time::Duration,
};

use anomaly::fail;
use bitcoin::hashes::hex::ToHex;

use crossbeam_channel as channel;
use prost::Message;
use prost_types::Any;
use tokio::runtime::Runtime as TokioRuntime;

use tendermint_proto::crypto::ProofOps;
use tendermint_proto::Protobuf;

use tendermint::abci::Path as TendermintABCIPath;
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::consensus::Params;

use tendermint_light_client::types::LightBlock as TMLightBlock;
use tendermint_rpc::{Client, HttpClient, Order};

use ibc_proto::cosmos::base::v1beta1::Coin;

use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};

use ibc::downcast;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics07_tendermint::header::Header as TMHeader;

use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics23_commitment::merkle::MerkleProof;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics24_host::Path::ClientConsensusState as ClientConsensusPath;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use ibc::Height as ICSHeight;

use super::Chain;

use crate::chain::QueryResponse;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::event::monitor::{EventBatch, EventMonitor};
use crate::keyring::store::{KeyEntry, KeyRing, KeyRingOperations, StoreBackend};
use crate::light_client::tendermint::LightClient as TMLightClient;
use crate::light_client::LightClient;

// Support for GRPC
use crate::chain::handle::QueryPacketDataRequest;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use ibc_proto::ibc::core::channel::v1::{
    PacketAckCommitment, QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};
use tonic::codegen::http::Uri;

// TODO size this properly
const DEFAULT_MAX_GAS: u64 = 300000;
const DEFAULT_MAX_TX_NUM: usize = 4;
const DEFAULT_MAX_TX_SIZE: usize = 2 * 1048576; // 2 MBytes

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    rt: Arc<Mutex<TokioRuntime>>,
    keybase: KeyRing,
}

impl CosmosSDKChain {
    /// The unbonding period of this chain
    pub fn unbonding_period(&self) -> Result<Duration, Error> {
        // TODO - generalize this
        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;

        let mut client = self
            .block_on(
                ibc_proto::cosmos::staking::v1beta1::query_client::QueryClient::connect(grpc_addr),
            )?
            .map_err(|e| Kind::Grpc.context(e))?;

        let request =
            tonic::Request::new(ibc_proto::cosmos::staking::v1beta1::QueryParamsRequest {});

        let response = self
            .block_on(client.params(request))?
            .map_err(|e| Kind::Grpc.context(e))?;

        let res = response
            .into_inner()
            .params
            .ok_or_else(|| Kind::Grpc.context("none staking params".to_string()))?
            .unbonding_time
            .ok_or_else(|| Kind::Grpc.context("none unbonding time".to_string()))?;

        Ok(Duration::from_secs(res.seconds as u64))
    }

    fn rpc_client(&self) -> &HttpClient {
        &self.rpc_client
    }

    pub fn config(&self) -> &ChainConfig {
        &self.config
    }

    /// Query the consensus parameters via an RPC query
    /// Specific to the SDK and used only for Tendermint client create
    pub fn query_consensus_params(&self) -> Result<Params, Error> {
        Ok(self
            .block_on(self.rpc_client().genesis())?
            .map_err(|e| Kind::Rpc.context(e))?
            .consensus_params)
    }

    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> Result<F::Output, Error> {
        Ok(self.rt.lock().map_err(|_| Kind::PoisonedMutex)?.block_on(f))
    }

    fn send_tx(&self, proto_msgs: Vec<Any>) -> Result<String, Error> {
        let key = self
            .keybase()
            .get_key()
            .map_err(|e| Kind::KeyBase.context(e))?;
        // Create TxBody
        let body = TxBody {
            messages: proto_msgs.to_vec(),
            memo: "".to_string(),
            timeout_height: 0_u64,
            extension_options: Vec::<Any>::new(),
            non_critical_extension_options: Vec::<Any>::new(),
        };

        // A protobuf serialization of a TxBody
        let mut body_buf = Vec::new();
        prost::Message::encode(&body, &mut body_buf).unwrap();

        let mut pk_buf = Vec::new();
        prost::Message::encode(&key.public_key.public_key.to_bytes(), &mut pk_buf).unwrap();

        // Create a MsgSend proto Any message
        let pk_any = Any {
            type_url: "/cosmos.crypto.secp256k1.PubKey".to_string(),
            value: pk_buf,
        };

        let acct_response = self
            .block_on(query_account(self, key.account))?
            .map_err(|e| Kind::Grpc.context(e))?;

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
            gas_limit: self.gas(),
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
        let signed = self.keybase.sign_msg(signdoc_buf);

        let tx_raw = TxRaw {
            body_bytes: body_buf,
            auth_info_bytes: auth_buf,
            signatures: vec![signed],
        };

        let mut txraw_buf = Vec::new();
        prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();

        let response = self
            .block_on(broadcast_tx_commit(self, txraw_buf))?
            .map_err(|e| Kind::Rpc.context(e))?;

        Ok(response)
    }

    fn gas(&self) -> u64 {
        self.config.gas.unwrap_or(DEFAULT_MAX_GAS)
    }

    fn max_tx_num(&self) -> usize {
        self.config.max_tx_num.unwrap_or(DEFAULT_MAX_TX_NUM)
    }

    fn max_tx_size(&self) -> usize {
        self.config.max_tx_num.unwrap_or(DEFAULT_MAX_TX_SIZE)
    }
}

impl Chain for CosmosSDKChain {
    type LightBlock = TMLightBlock;
    type Header = TMHeader;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;

    fn bootstrap(config: ChainConfig, rt: Arc<Mutex<TokioRuntime>>) -> Result<Self, Error> {
        let rpc_client =
            HttpClient::new(config.rpc_addr.clone()).map_err(|e| Kind::Rpc.context(e))?;

        // Initialize key store and load key
        let key_store = KeyRing::init(StoreBackend::Test, config.clone())
            .map_err(|e| Kind::KeyBase.context(e))?;

        Ok(Self {
            rt,
            config,
            keybase: key_store,
            rpc_client,
        })
    }

    // TODO use a simpler approach to create the light client
    #[allow(clippy::type_complexity)]
    fn init_light_client(
        &self,
    ) -> Result<(Box<dyn LightClient<Self>>, Option<thread::JoinHandle<()>>), Error> {
        let (lc, supervisor) = TMLightClient::from_config(&self.config, true)?;

        let supervisor_thread = thread::spawn(move || supervisor.run().unwrap());

        Ok((Box::new(lc), Some(supervisor_thread)))
    }

    fn init_event_monitor(
        &self,
        rt: Arc<Mutex<TokioRuntime>>,
    ) -> Result<
        (
            channel::Receiver<EventBatch>,
            Option<thread::JoinHandle<()>>,
        ),
        Error,
    > {
        let (mut event_monitor, event_receiver) =
            EventMonitor::new(self.config.id.clone(), self.config.rpc_addr.clone(), rt)?;

        event_monitor.subscribe().unwrap();
        let monitor_thread = thread::spawn(move || event_monitor.run());

        Ok((event_receiver, Some(monitor_thread)))
    }

    fn id(&self) -> &ChainId {
        &self.config().id
    }

    fn keybase(&self) -> &KeyRing {
        &self.keybase
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

        let response =
            self.block_on(abci_query(&self, path, data.to_string(), height, prove))??;

        // TODO - Verify response proof, if requested.
        if prove {}

        Ok(response)
    }

    /// Send one or more transactions that include all the specified messages
    fn send_msgs(&mut self, proto_msgs: Vec<Any>) -> Result<Vec<String>, Error> {
        if proto_msgs.is_empty() {
            return Ok(vec!["No messages to send".to_string()]);
        }
        let mut res = vec![];

        let mut n = 0;
        let mut size = 0;
        let mut msg_batch = vec![];
        for msg in proto_msgs.iter() {
            msg_batch.append(&mut vec![msg.clone()]);
            let mut buf = Vec::new();
            prost::Message::encode(msg, &mut buf).unwrap();
            n += 1;
            size += buf.len();
            if n >= self.max_tx_num() || size >= self.max_tx_size() {
                let result = self.send_tx(msg_batch)?;
                res.append(&mut vec![result]);
                n = 0;
                size = 0;
                msg_batch = vec![];
            }
        }
        if !msg_batch.is_empty() {
            let result = self.send_tx(msg_batch)?;
            res.append(&mut vec![result]);
        }
        Ok(res)
    }

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<ICSHeight, Error> {
        let status = self
            .block_on(self.rpc_client().status())?
            .map_err(|e| Kind::Rpc.context(e))?;

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
        let client_state = self
            .query(ClientStatePath(client_id.clone()), height, false)
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| {
                AnyClientState::decode_vec(&v.value).map_err(|e| Kind::Query.context(e))
            })?;
        let client_state = downcast!(client_state => AnyClientState::Tendermint)
            .ok_or_else(|| Kind::Query.context("unexpected client state type"))?;
        Ok(client_state)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        // TODO - do a real chain query
        Ok(CommitmentPrefix::from(
            self.config().store_prefix.as_bytes().to_vec(),
        ))
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        let res = self
            .query(ClientStatePath(client_id.clone()), height, true)
            .map_err(|e| Kind::Query.context(e))?;

        let client_state =
            AnyClientState::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        let client_state = downcast!(client_state => AnyClientState::Tendermint)
            .ok_or_else(|| Kind::Query.context("unexpected client state type"))?;

        Ok((client_state, res.proof))
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
            AnyConsensusState::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        let consensus_state = downcast!(consensus_state => AnyConsensusState::Tendermint)
            .ok_or_else(|| Kind::Query.context("unexpected client consensus type"))?;

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
            signed_header: target_light_block.signed_header.clone(),
            validator_set: target_light_block.validators,
            trusted_validator_set: trusted_light_block.validators,
        })
    }

    /// Get the account for the signer
    fn get_signer(&mut self) -> Result<AccountId, Error> {
        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key()
            .map_err(|e| Kind::KeyBase.context(e))?;

        let signer: AccountId =
            AccountId::from_str(&key.address.to_hex()).map_err(|e| Kind::KeyBase.context(e))?;

        Ok(signer)
    }

    /// Get the signing key
    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key()
            .map_err(|e| Kind::KeyBase.context(e))?;

        Ok(key)
    }
    /// Queries the packet commitment hashes associated with a channel.
    /// TODO - move the chain trait
    /// Note: the result Vec<PacketAckCommitment> has an awkward name but fixed in a future IBC proto variant
    /// It will move to Vec<PacketState>
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketAckCommitment>, ICSHeight), Error> {
        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )?
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.packet_commitments(request))?
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        let pc = response.commitments;

        let height = response
            .height
            .ok_or_else(|| Kind::Grpc.context("missing height in response"))?
            .try_into()
            .map_err(|_| Kind::Grpc.context("invalid height in response"))?;
        Ok((pc, height))
    }

    /// Queries the packet commitment hashes associated with a channel.
    /// TODO - move the chain trait
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )?
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.unreceived_packets(request))?
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        Ok(response.sequences)
    }

    /// Queries the packet data for all packets with sequences included in the request.
    /// Note - there is no way to format the query such that it asks for Tx-es with either
    /// sequence (the query conditions can only be AND-ed)
    /// There is a possibility to include "<=" and ">=" conditions but it doesn't work with
    /// string attributes (sequence is emmitted as a string).
    /// Therefore, here we perform one tx_search for each query. Alternatively, a single query
    /// for all packets could be performed but it would return all packets ever sent.
    fn query_packet_data(&self, request: QueryPacketDataRequest) -> Result<Vec<Packet>, Error> {
        let mut result: Vec<Packet> = vec![];
        for seq in request.sequences.iter() {
            let query = tendermint_rpc::query::Query::eq(
                "send_packet.packet_src_channel",
                request.channel_id.clone(),
            )
            .and_eq("send_packet.packet_src_port", request.port_id.clone())
            .and_eq("send_packet.packet_sequence", seq.to_string());
            let response = self
                .block_on(
                    self.rpc_client
                        .tx_search(query, false, 1, 1, Order::Ascending),
                )
                .unwrap()
                .unwrap(); // todo

            let mut packets = packet_from_tx_search_response(request.clone(), response.clone())?;
            result.append(&mut packets);
        }
        Ok(result)
    }
}

use ibc::ics04_channel::packet::Packet;
use ibc_proto::ibc::core::channel::v1::Packet as RawPacket;
use std::collections::HashSet;
use subtle_encoding::base64;
use std::convert::TryInto;

// Extract the packets from the query_tx RPC response. The response includes the full set of events
// from the Tx-es where there is at least one request query match.
// For example, the query request asks for the Tx for packet with sequence 3, and both 3 and 4 were
// committed in one Tx. In this case the response includes the events for 3 and 4.
fn packet_from_tx_search_response(
    request: QueryPacketDataRequest,
    response: tendermint_rpc::endpoint::tx_search::Response,
) -> Result<Vec<Packet>, Error> {
    let mut packets: Vec<Packet> = vec![];
    let mut seqs: HashSet<u64> = request.sequences.iter().cloned().collect();
    for r in response.txs.iter() {
        let events: Vec<tendermint::abci::Event> = r.clone().tx_result.events;
        let mut packet = RawPacket {
            sequence: 0,
            source_port: "".to_string(),
            source_channel: "".to_string(),
            destination_port: "".to_string(),
            destination_channel: "".to_string(),
            data: vec![],
            timeout_height: None,
            timeout_timestamp: 0,
        };
        for e in events.iter() {
            if e.type_str == *"send_packet" {
                for a in e.attributes.iter() {
                    let key =
                        String::from_utf8(base64::decode(a.key.to_string().as_bytes()).unwrap())
                            .unwrap();
                    let value =
                        String::from_utf8(base64::decode(a.value.to_string().as_bytes()).unwrap())
                            .unwrap();
                    match key.as_str() {
                        "packet_src_channel" => packet.source_channel = value,
                        "packet_src_port" => packet.source_port = value,
                        "packet_sequence" => packet.sequence = value.parse::<u64>().unwrap(),
                        "packet_dst_channel" => packet.destination_channel = value,
                        "packet_dst_port" => packet.destination_port = value,
                        "packet_data" => packet.data = Vec::from(value.as_bytes()),
                        "packet_timeout_height" => {
                            let to: Vec<&str> = value.split('-').collect();
                            packet.timeout_height =
                                Some(ibc_proto::ibc::core::client::v1::Height {
                                    version_number: to[0].parse::<u64>().unwrap(),
                                    version_height: to[1].parse::<u64>().unwrap(),
                                });
                        }
                        _ => {}
                    };
                }
                if request.port_id == packet.source_port
                    && request.channel_id == packet.source_channel
                    && seqs.contains(&packet.sequence)
                {
                    packets.append(&mut vec![packet.clone().try_into().unwrap()]);
                    seqs.remove(&packet.sequence);
                }
            }
        }
    }
    Ok(packets)
}

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
async fn abci_query(
    chain: &CosmosSDKChain,
    path: TendermintABCIPath,
    data: String,
    height: Height,
    prove: bool,
) -> Result<QueryResponse, Error> {
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

/// Perform a `broadcast_tx_commit`, and return the corresponding deserialized response data.
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

/// Uses the GRPC client to retrieve the account sequence
async fn query_account(chain: &CosmosSDKChain, address: String) -> Result<BaseAccount, Error> {
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
