use std::{
    convert::TryFrom, convert::TryInto, future::Future, str::FromStr, sync::Arc, thread,
    time::Duration,
};

use anomaly::fail;
use bitcoin::hashes::hex::ToHex;

use crossbeam_channel as channel;
use prost::Message;
use prost_types::Any;
use tokio::runtime::Runtime as TokioRuntime;
use tonic::codegen::http::Uri;

use tendermint_proto::Protobuf;

use tendermint_rpc::query::Query;

use tendermint::abci::Path as TendermintABCIPath;
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::consensus::Params;

use tendermint_light_client::types::LightBlock as TMLightBlock;
use tendermint_rpc::{endpoint::broadcast::tx_commit::Response, Client, HttpClient, Order};

use ibc_proto::cosmos::base::v1beta1::Coin;

use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
// Support for GRPC
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryConnectionChannelsRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use ibc::downcast;
use ibc::events::{from_tx_response_event, IBCEvent};
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics04_channel::channel::QueryPacketEventDataRequest;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use ibc::ics07_tendermint::header::Header as TMHeader;

use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId};
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
use ibc::ics03_connection::raw::ConnectionIds;
use ibc::ics04_channel::packet::Sequence;
use ibc_proto::ibc::core::connection::v1::QueryConnectionsRequest;

// TODO size this properly
const DEFAULT_MAX_GAS: u64 = 300000;
const DEFAULT_MAX_MSG_NUM: usize = 30;
const DEFAULT_MAX_TX_SIZE: usize = 2 * 1048576; // 2 MBytes

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    rt: Arc<TokioRuntime>,
    keybase: KeyRing,
}

impl CosmosSDKChain {
    /// The unbonding period of this chain
    pub fn unbonding_period(&self) -> Result<Duration, Error> {
        crate::time!("unbonding_period");

        // TODO - generalize this
        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;

        let mut client = self
            .block_on(
                ibc_proto::cosmos::staking::v1beta1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request =
            tonic::Request::new(ibc_proto::cosmos::staking::v1beta1::QueryParamsRequest {});

        let response = self
            .block_on(client.params(request))
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
        crate::time!("query_consensus_params");

        Ok(self
            .block_on(self.rpc_client().genesis())
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?
            .consensus_params)
    }

    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        crate::time!("block_on");
        self.rt.block_on(f)
    }

    fn send_tx(&self, proto_msgs: Vec<Any>) -> Result<Vec<IBCEvent>, Error> {
        crate::time!("send_tx");

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
            .block_on(query_account(self, key.account))
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
            .block_on(broadcast_tx_commit(self, txraw_buf))
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?;

        let res = tx_result_to_event(response)?;

        Ok(res)
    }

    fn gas(&self) -> u64 {
        self.config.gas.unwrap_or(DEFAULT_MAX_GAS)
    }

    fn max_msg_num(&self) -> usize {
        self.config.max_msg_num.unwrap_or(DEFAULT_MAX_MSG_NUM)
    }

    fn max_tx_size(&self) -> usize {
        self.config.max_tx_size.unwrap_or(DEFAULT_MAX_TX_SIZE)
    }
}

impl Chain for CosmosSDKChain {
    type LightBlock = TMLightBlock;
    type Header = TMHeader;
    type ConsensusState = TMConsensusState;
    type ClientState = ClientState;

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Kind::Rpc(config.rpc_addr.clone()).context(e))?;

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
        crate::time!("init_light_client");

        let (lc, supervisor) = TMLightClient::from_config(&self.config, true)?;

        let supervisor_thread = thread::spawn(move || supervisor.run().unwrap());

        Ok((Box::new(lc), Some(supervisor_thread)))
    }

    fn init_event_monitor(
        &self,
        rt: Arc<TokioRuntime>,
    ) -> Result<
        (
            channel::Receiver<EventBatch>,
            Option<thread::JoinHandle<()>>,
        ),
        Error,
    > {
        crate::time!("init_event_monitor");

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
        crate::time!("query");

        let path = TendermintABCIPath::from_str(IBC_QUERY_PATH).unwrap();

        let height =
            Height::try_from(height.revision_height).map_err(|e| Kind::InvalidHeight.context(e))?;

        if !data.is_provable() & prove {
            return Err(Kind::Store
                .context("requested proof for a path in the privateStore")
                .into());
        }

        let response = self.block_on(abci_query(&self, path, data.to_string(), height, prove))?;

        // TODO - Verify response proof, if requested.
        if prove {}

        Ok(response)
    }

    /// Send one or more transactions that include all the specified messages
    fn send_msgs(&mut self, proto_msgs: Vec<Any>) -> Result<Vec<IBCEvent>, Error> {
        crate::time!("send_msgs");

        if proto_msgs.is_empty() {
            return Ok(vec![IBCEvent::Empty("No messages to send".to_string())]);
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
            if n >= self.max_msg_num() || size >= self.max_tx_size() {
                let mut result = self.send_tx(msg_batch)?;
                res.append(&mut result);
                n = 0;
                size = 0;
                msg_batch = vec![];
            }
        }
        if !msg_batch.is_empty() {
            let mut result = self.send_tx(msg_batch)?;
            res.append(&mut result);
        }

        Ok(res)
    }

    fn build_client_state(&self, height: ICSHeight) -> Result<Self::ClientState, Error> {
        // Build the client state.
        Ok(ibc::ics07_tendermint::client_state::ClientState::new(
            self.id().to_string(),
            self.config.trust_threshold,
            self.config.trusting_period,
            self.unbonding_period()?,
            Duration::from_millis(3000), // TODO - get it from src config when avail
            height,
            ICSHeight::zero(),
            vec!["upgrade".to_string(), "upgradedIBCState".to_string()],
            false,
            false,
        )
        .map_err(|e| Kind::BuildClientStateFailure.context(e))?)
    }

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<ICSHeight, Error> {
        crate::time!("query_latest_height");

        let status = self
            .block_on(self.rpc_client().status())
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?;

        if status.sync_info.catching_up {
            fail!(
                Kind::LightClientSupervisor(self.config.id.clone()),
                "node at {} running chain {} not caught up",
                self.config().rpc_addr,
                self.config().id,
            );
        }

        Ok(ICSHeight {
            revision_number: ChainId::chain_version(status.node_info.network.as_str()),
            revision_height: u64::from(status.sync_info.latest_block_height),
        })
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<Self::ClientState, Error> {
        crate::time!("query_client_state");

        let client_state = self
            .query(ClientStatePath(client_id.clone()), height, false)
            .map_err(|e| Kind::Query("client state".into()).context(e))
            .and_then(|v| {
                AnyClientState::decode_vec(&v.value)
                    .map_err(|e| Kind::Query("client state".into()).context(e))
            })?;
        let client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                Kind::Query("client state".into()).context("unexpected client state type")
            })?;
        Ok(client_state)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        crate::time!("query_commitment_prefix");

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
        crate::time!("proven_client_state");

        let res = self
            .query(ClientStatePath(client_id.clone()), height, true)
            .map_err(|e| Kind::Query("client state".into()).context(e))?;

        let client_state = AnyClientState::decode_vec(&res.value)
            .map_err(|e| Kind::Query("client state".into()).context(e))?;

        let client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                Kind::Query("client state".into()).context("unexpected client state type")
            })?;

        Ok((
            client_state,
            res.proof.ok_or_else(|| {
                Kind::Query("client state".into()).context("empty proof".to_string())
            })?,
        ))
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: ICSHeight,
        height: ICSHeight,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        crate::time!("proven_client_consensus");

        let res = self
            .query(
                ClientConsensusPath {
                    client_id: client_id.clone(),
                    epoch: consensus_height.revision_number,
                    height: consensus_height.revision_height,
                },
                height,
                true,
            )
            .map_err(|e| Kind::Query("client consensus".into()).context(e))?;

        let consensus_state = AnyConsensusState::decode_vec(&res.value)
            .map_err(|e| Kind::Query("client consensus".into()).context(e))?;

        let consensus_state = downcast!(consensus_state => AnyConsensusState::Tendermint)
            .ok_or_else(|| {
                Kind::Query("client consensus".into()).context("unexpected client consensus type")
            })?;

        Ok((
            consensus_state,
            res.proof.ok_or_else(|| {
                Kind::Query("client consensus".into()).context("empty proof".to_string())
            })?,
        ))
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        crate::time!("build_consensus_state");

        Ok(TMConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &self,
        trusted_light_block: Self::LightBlock,
        target_light_block: Self::LightBlock,
    ) -> Result<Self::Header, Error> {
        crate::time!("build_header");

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
        crate::time!("get_signer");

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
        crate::time!("get_key");

        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key()
            .map_err(|e| Kind::KeyBase.context(e))?;

        Ok(key)
    }

    /// Queries the packet commitment hashes associated with a channel.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, ICSHeight), Error> {
        crate::time!("query_packet_commitments");

        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.packet_commitments(request))
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
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        crate::time!("query_unreceived_packets");

        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.unreceived_packets(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        Ok(response.sequences)
    }

    /// Queries the packet acknowledgment hashes associated with a channel.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, ICSHeight), Error> {
        crate::time!("query_packet_acknowledgements");

        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.packet_acknowledgements(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        let pc = response.acknowledgements;

        let height = response
            .height
            .ok_or_else(|| Kind::Grpc.context("missing height in response"))?
            .try_into()
            .map_err(|_| Kind::Grpc.context("invalid height in response"))?;

        Ok((pc, height))
    }

    /// Queries the packet commitment hashes associated with a channel.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        crate::time!("query_unreceived_acknowledgements");

        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.unreceived_acks(request))
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
    fn query_txs(&self, request: QueryPacketEventDataRequest) -> Result<Vec<IBCEvent>, Error> {
        crate::time!("query_txs");

        let mut result: Vec<IBCEvent> = vec![];

        for seq in request.sequences.iter() {
            // query all Tx-es that include events related to packet with given port, channel and sequence
            let response = self
                .block_on(self.rpc_client.tx_search(
                    packet_query(&request, seq)?,
                    false,
                    1,
                    1,
                    Order::Ascending,
                ))
                .unwrap(); // todo

            let mut events = packet_from_tx_search_response(&request, *seq, &response)?
                .map_or(vec![], |v| vec![v]);
            result.append(&mut events);
        }
        Ok(result)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<ChannelId>, Error> {
        crate::time!("query_connection_channels");

        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.connection_channels(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        // TODO: add warnings for any identifiers that fail to parse (below).
        //  https://github.com/informalsystems/ibc-rs/pull/506#discussion_r555945560

        let vec_ids = response
            .channels
            .iter()
            .filter_map(|ic| ChannelId::from_str(ic.channel_id.as_str()).ok())
            .collect();

        Ok(vec_ids)
    }

    fn query_connections(&self, request: QueryConnectionsRequest) -> Result<ConnectionIds, Error> {
        crate::time!("query_connections");

        let grpc_addr =
            Uri::from_str(&self.config().grpc_addr).map_err(|e| Kind::Grpc.context(e))?;
        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(grpc_addr),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.connections(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        // TODO: add warnings for any identifiers that fail to parse (below).
        //      similar to the parsing in `query_connection_channels`.

        let ids = response
            .connections
            .iter()
            .filter_map(|ic| ConnectionId::from_str(ic.id.as_str()).ok())
            .collect();

        Ok(ids)
    }
}

fn packet_query(request: &QueryPacketEventDataRequest, seq: &Sequence) -> Result<Query, Error> {
    Ok(tendermint_rpc::query::Query::eq(
        format!("{}.packet_src_channel", request.event_id.as_str()),
        request.source_channel_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_src_port", request.event_id.as_str()),
        request.source_port_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_sequence", request.event_id.as_str()),
        seq.to_string(),
    ))
}

// Extract the packet events from the query_tx RPC response. The response includes the full set of events
// from the Tx-es where there is at least one request query match.
// For example, the query request asks for the Tx for packet with sequence 3, and both 3 and 4 were
// committed in one Tx. In this case the response includes the events for 3 and 4.
fn packet_from_tx_search_response(
    request: &QueryPacketEventDataRequest,
    seq: Sequence,
    response: &tendermint_rpc::endpoint::tx_search::Response,
) -> Result<Option<IBCEvent>, Error> {
    for r in response.txs.iter() {
        let height = r.height;
        if height.value() > request.height.revision_height {
            continue;
        }

        for e in r.tx_result.events.iter() {
            if e.type_str != request.event_id.as_str() {
                continue;
            }

            let res = from_tx_response_event(e);
            if res.is_none() {
                continue;
            }
            let event = res.unwrap();
            let packet = match &event {
                IBCEvent::SendPacketChannel(send_ev) => Some(&send_ev.packet),
                IBCEvent::WriteAcknowledgementChannel(ack_ev) => Some(&ack_ev.packet),
                _ => None,
            };

            if packet.is_none() {
                continue;
            }

            let packet = packet.unwrap();
            if packet.source_port != request.source_port_id
                || packet.source_channel != request.source_channel_id
                || packet.sequence != seq
            {
                continue;
            }

            return Ok(Some(event));
        }
    }
    Ok(None)
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
        .map_err(|e| Kind::Rpc(chain.config.rpc_addr.clone()).context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        return Err(Kind::Rpc(chain.config.rpc_addr.clone())
            .context(response.log.to_string())
            .into());
    }

    if prove && response.proof.is_none() {
        // Fail due to empty proof
        return Err(Kind::EmptyResponseProof.into());
    }

    let raw_proof_ops = response.proof;

    let response = QueryResponse {
        value: response.value,
        proof: convert_tm_to_ics_merkle_proof(raw_proof_ops).unwrap(),
        height: response.height,
    };

    Ok(response)
}

/// Perform a `broadcast_tx_commit`, and return the corresponding deserialized response data.
async fn broadcast_tx_commit(
    chain: &CosmosSDKChain,
    data: Vec<u8>,
) -> Result<Response, anomaly::Error<Kind>> {
    let response = chain
        .rpc_client()
        .broadcast_tx_commit(data.into())
        .await
        .map_err(|e| Kind::Rpc(chain.config.rpc_addr.clone()).context(e))?;

    Ok(response)
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

pub fn tx_result_to_event(response: Response) -> Result<Vec<IBCEvent>, anomaly::Error<Kind>> {
    let mut result = vec![];

    // Verify the return codes from check_tx and deliver_tx
    if response.check_tx.code.is_err() {
        return Ok(vec![IBCEvent::ChainError(format!(
            "check_tx reports error: log={:?}",
            response.check_tx.log
        ))]);
    }
    if response.deliver_tx.code.is_err() {
        return Ok(vec![IBCEvent::ChainError(format!(
            "deliver_tx reports error: log={:?}",
            response.deliver_tx.log
        ))]);
    }

    for event in response.deliver_tx.events {
        if let Some(ibc_ev) = from_tx_response_event(&event) {
            result.push(ibc_ev);
        }
    }
    Ok(result)
}
