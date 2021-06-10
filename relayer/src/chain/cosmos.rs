use std::{
    convert::TryFrom, convert::TryInto, future::Future, ops::Deref, str::FromStr, sync::Arc,
    thread, time::Duration,
};

use bech32::{ToBase32, Variant};
use bitcoin::hashes::hex::ToHex;
use prost::Message;
use prost_types::Any;
use tendermint::abci::Path as TendermintABCIPath;
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::consensus::Params;
use tendermint_light_client::types::LightBlock as TMLightBlock;
use tendermint_proto::Protobuf;
use tendermint_rpc::query::Query;
use tendermint_rpc::{endpoint::broadcast::tx_commit::Response, Client, HttpClient, Order};
use tokio::runtime::Runtime as TokioRuntime;
use tonic::codegen::http::Uri;
use tonic::Code;

use ibc::downcast;
use ibc::events::{from_tx_response_event, IbcEvent};
use ibc::ics02_client::client_consensus::{
    AnyConsensusState, AnyConsensusStateWithHeight, QueryClientEventRequest,
};
use ibc::ics02_client::client_state::{AnyClientState, IdentifiedAnyClientState};
use ibc::ics02_client::events as ClientEvents;
use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd, QueryPacketEventDataRequest};
use ibc::ics04_channel::events as ChannelEvents;
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics07_tendermint::client_state::{AllowUpdate, ClientState};
use ibc::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use ibc::ics07_tendermint::header::Header as TmHeader;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::ics24_host::Path::ClientConsensusState as ClientConsensusPath;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::ics24_host::{ClientUpgradePath, Path, IBC_QUERY_PATH, SDK_UPGRADE_QUERY_PATH};
use ibc::query::QueryTxRequest;
use ibc::signer::Signer;
use ibc::Height as ICSHeight;
// Support for GRPC
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
use ibc_proto::cosmos::upgrade::v1beta1::{
    QueryCurrentPlanRequest, QueryUpgradedConsensusStateRequest,
};
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryChannelClientStateRequest, QueryChannelsRequest,
    QueryConnectionChannelsRequest, QueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest,
    QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::{QueryClientStatesRequest, QueryConsensusStatesRequest};
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::ibc::core::connection::v1::{
    QueryClientConnectionsRequest, QueryConnectionsRequest,
};

use crate::chain::QueryResponse;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::event::monitor::{EventMonitor, EventReceiver};
use crate::keyring::{KeyEntry, KeyRing, Store};
use crate::light_client::tendermint::LightClient as TmLightClient;
use crate::light_client::LightClient;
use crate::light_client::Verified;

use super::Chain;
use tendermint_rpc::endpoint::tx_search::ResultTx;

// TODO size this properly
const DEFAULT_MAX_GAS: u64 = 300000;
const DEFAULT_MAX_MSG_NUM: usize = 30;
const DEFAULT_MAX_TX_SIZE: usize = 2 * 1048576; // 2 MBytes
const DEFAULT_GAS_FEE_AMOUNT: u64 = 1000;

pub struct CosmosSdkChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    grpc_addr: Uri,
    rt: Arc<TokioRuntime>,
    keybase: KeyRing,
}

impl CosmosSdkChain {
    /// The unbonding period of this chain
    pub fn unbonding_period(&self) -> Result<Duration, Error> {
        crate::time!("unbonding_period");

        let mut client = self
            .block_on(
                ibc_proto::cosmos::staking::v1beta1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
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

        Ok(Duration::new(res.seconds as u64, res.nanos as u32))
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

    fn send_tx(&self, proto_msgs: Vec<Any>) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("send_tx");

        let key = self
            .keybase()
            .get_key(&self.config.key_name)
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

        crate::time!("PK {:?}", hex::encode(key.public_key.public_key.to_bytes()));

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

        let fee = Some(Fee {
            amount: vec![self.fee()],
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
            account_number: acct_response.account_number,
        };

        // A protobuf serialization of a SignDoc
        let mut signdoc_buf = Vec::new();
        prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

        // Sign doc and broadcast
        let signed = self
            .keybase
            .sign_msg(&self.config.key_name, signdoc_buf)
            .map_err(|e| Kind::KeyBase.context(e))?;

        let tx_raw = TxRaw {
            body_bytes: body_buf,
            auth_info_bytes: auth_buf,
            signatures: vec![signed],
        };

        let mut txraw_buf = Vec::new();
        prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();

        crate::time!("TxRAW {:?}", hex::encode(txraw_buf.clone()));

        let response = self
            .block_on(broadcast_tx_commit(self, txraw_buf))
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?;

        let res = tx_result_to_event(&self.config.id, response)?;

        Ok(res)
    }

    fn gas(&self) -> u64 {
        self.config.gas.unwrap_or(DEFAULT_MAX_GAS)
    }

    fn fee(&self) -> Coin {
        let amount = self
            .config
            .clone()
            .fee_amount
            .unwrap_or(DEFAULT_GAS_FEE_AMOUNT);

        Coin {
            denom: self.config.fee_denom.clone(),
            amount: amount.to_string(),
        }
    }

    fn max_msg_num(&self) -> usize {
        self.config.max_msg_num.unwrap_or(DEFAULT_MAX_MSG_NUM)
    }

    fn max_tx_size(&self) -> usize {
        self.config.max_tx_size.unwrap_or(DEFAULT_MAX_TX_SIZE)
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

    // Perform an ABCI query against the client upgrade sub-store to fetch a proof.
    fn query_client_upgrade_proof(
        &self,
        data: ClientUpgradePath,
        height: Height,
    ) -> Result<(MerkleProof, ICSHeight), Error> {
        let prev_height =
            Height::try_from(height.value() - 1).map_err(|e| Kind::InvalidHeight.context(e))?;

        let path = TendermintABCIPath::from_str(SDK_UPGRADE_QUERY_PATH).unwrap();
        let response = self.block_on(abci_query(
            &self,
            path,
            Path::Upgrade(data).to_string(),
            prev_height,
            true,
        ))?;

        let proof = response.proof.ok_or(Kind::EmptyResponseProof)?;

        let height = ICSHeight::new(
            self.config.id.version(),
            response.height.increment().value(),
        );

        Ok((proof, height))
    }
}

impl Chain for CosmosSdkChain {
    type LightBlock = TMLightBlock;
    type Header = TmHeader;
    type ConsensusState = TMConsensusState;
    type ClientState = ClientState;

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Kind::Rpc(config.rpc_addr.clone()).context(e))?;

        // Initialize key store and load key
        let keybase = KeyRing::new(Store::Test, &config.account_prefix, &config.id)
            .map_err(|e| Kind::KeyBase.context(e))?;

        let grpc_addr =
            Uri::from_str(&config.grpc_addr.to_string()).map_err(|e| Kind::Grpc.context(e))?;

        Ok(Self {
            config,
            rpc_client,
            grpc_addr,
            rt,
            keybase,
        })
    }

    fn init_light_client(&self) -> Result<Box<dyn LightClient<Self>>, Error> {
        use tendermint_light_client::types::PeerId;

        crate::time!("init_light_client");

        let peer_id: PeerId = self
            .rt
            .block_on(self.rpc_client.status())
            .map(|s| s.node_info.id)
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?;

        let light_client = TmLightClient::from_config(&self.config, peer_id)?;

        Ok(Box::new(light_client))
    }

    fn init_event_monitor(
        &self,
        rt: Arc<TokioRuntime>,
    ) -> Result<(EventReceiver, Option<thread::JoinHandle<()>>), Error> {
        crate::time!("init_event_monitor");

        let (mut event_monitor, event_receiver) = EventMonitor::new(
            self.config.id.clone(),
            self.config.websocket_addr.clone(),
            rt,
        )
        .map_err(Kind::EventMonitor)?;

        event_monitor.subscribe().map_err(Kind::EventMonitor)?;

        let monitor_thread = thread::spawn(move || event_monitor.run());

        Ok((event_receiver, Some(monitor_thread)))
    }

    fn id(&self) -> &ChainId {
        &self.config().id
    }

    fn keybase(&self) -> &KeyRing {
        &self.keybase
    }

    fn keybase_mut(&mut self) -> &mut KeyRing {
        &mut self.keybase
    }

    /// Send one or more transactions that include all the specified messages
    fn send_msgs(&mut self, proto_msgs: Vec<Any>) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("send_msgs");

        if proto_msgs.is_empty() {
            return Ok(vec![IbcEvent::Empty("No messages to send".to_string())]);
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

    /// Get the account for the signer
    fn get_signer(&mut self) -> Result<Signer, Error> {
        crate::time!("get_signer");

        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key(&self.config.key_name)
            .map_err(|e| Kind::KeyBase.context(e))?;

        let bech32 = encode_to_bech32(&key.address.to_hex(), &self.config.account_prefix)?;
        Ok(Signer::new(bech32))
    }

    /// Get the signing key
    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        crate::time!("get_key");

        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key(&self.config.key_name)
            .map_err(|e| Kind::KeyBase.context(e))?;

        Ok(key)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        crate::time!("query_commitment_prefix");

        // TODO - do a real chain query
        Ok(CommitmentPrefix::from(
            self.config().store_prefix.as_bytes().to_vec(),
        ))
    }

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<ICSHeight, Error> {
        crate::time!("query_latest_height");

        let status = self
            .block_on(self.rpc_client().status())
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?;

        if status.sync_info.catching_up {
            Err(Kind::LightClientNotUpToDate(
                self.config.rpc_addr.clone(),
                self.config().id.clone(),
            )
            .into())
        } else {
            Ok(ICSHeight {
                revision_number: ChainId::chain_version(status.node_info.network.as_str()),
                revision_height: u64::from(status.sync_info.latest_block_height),
            })
        }
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        crate::time!("query_chain_clients");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);
        let response = self
            .block_on(client.client_states(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        // Deserialize into domain type
        let mut clients: Vec<IdentifiedAnyClientState> = response
            .client_states
            .into_iter()
            .filter_map(|cs| IdentifiedAnyClientState::try_from(cs).ok())
            .collect();

        // Sort by client identifier counter
        clients.sort_by(|a, b| {
            client_id_suffix(&a.client_id)
                .unwrap_or(0) // Fallback to `0` suffix (no sorting) if client id is malformed
                .cmp(&client_id_suffix(&b.client_id).unwrap_or(0))
        });

        Ok(clients)
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<Self::ClientState, Error> {
        crate::time!("query_client_state");

        let response = self
            .query(ClientStatePath(client_id.clone()), height, false)
            .map_err(|e| Kind::Query("client state".into()).context(e))?;

        let raw_val = Any::decode(response.value.deref())
            .map_err(|e| Kind::Query("client state".into()).context(e))?;

        let client_state: AnyClientState =
            raw_val
                .try_into()
                .map_err(|e: ibc::ics02_client::error::Error| {
                    Kind::Ics002(e.kind().clone()).context(e)
                })?;

        let client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                Kind::Query("client state".into()).context("unexpected client state type")
            })?;

        Ok(client_state)
    }

    fn query_upgraded_client_state(
        &self,
        height: ICSHeight,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        crate::time!("query_upgraded_client_state");

        let mut client = self
            .block_on(
                ibc_proto::cosmos::upgrade::v1beta1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let req = tonic::Request::new(QueryCurrentPlanRequest {});
        let response = self
            .block_on(client.current_plan(req))
            .map_err(|e| Kind::Grpc.context(e))?;

        let upgraded_client_state_raw = response
            .into_inner()
            .plan
            .ok_or(Kind::EmptyResponseValue)?
            .upgraded_client_state
            .ok_or(Kind::EmptyUpgradedClientState)?;
        let client_state = AnyClientState::try_from(upgraded_client_state_raw)
            .map_err(|e| Kind::Grpc.context(e))?;

        // TODO: Better error kinds here.
        let tm_client_state =
            downcast!(client_state => AnyClientState::Tendermint).ok_or_else(|| {
                Kind::Query("upgraded client state".into()).context("unexpected client state type")
            })?;

        // Query for the proof.
        let tm_height =
            Height::try_from(height.revision_height).map_err(|e| Kind::InvalidHeight.context(e))?;
        let (proof, _proof_height) = self.query_client_upgrade_proof(
            ClientUpgradePath::UpgradedClientState(height.revision_height),
            tm_height,
        )?;

        Ok((tm_client_state, proof))
    }

    fn query_upgraded_consensus_state(
        &self,
        height: ICSHeight,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        crate::time!("query_upgraded_consensus_state");

        let tm_height =
            Height::try_from(height.revision_height).map_err(|e| Kind::InvalidHeight.context(e))?;

        let mut client = self
            .block_on(
                ibc_proto::cosmos::upgrade::v1beta1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let req = tonic::Request::new(QueryUpgradedConsensusStateRequest {
            last_height: tm_height.into(),
        });
        let response = self
            .block_on(client.upgraded_consensus_state(req))
            .map_err(|e| Kind::Grpc.context(e))?;

        let upgraded_consensus_state_raw = response
            .into_inner()
            .upgraded_consensus_state
            .ok_or(Kind::EmptyResponseValue)?;

        // TODO: More explicit error kinds (should not reuse Grpc all over the place)
        let consensus_state = AnyConsensusState::try_from(upgraded_consensus_state_raw)
            .map_err(|e| Kind::Grpc.context(e))?;

        let tm_consensus_state = downcast!(consensus_state => AnyConsensusState::Tendermint)
            .ok_or_else(|| {
                Kind::Query("upgraded consensus state".into())
                    .context("unexpected consensus state type")
            })?;

        // Fetch the proof.
        let (proof, _proof_height) = self.query_client_upgrade_proof(
            ClientUpgradePath::UpgradedClientConsensusState(height.revision_height),
            tm_height,
        )?;

        Ok((tm_consensus_state, proof))
    }

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        crate::time!("query_chain_clients");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);
        let response = self
            .block_on(client.consensus_states(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        let mut consensus_states: Vec<AnyConsensusStateWithHeight> = response
            .consensus_states
            .into_iter()
            .filter_map(|cs| TryFrom::try_from(cs).ok())
            .collect();
        consensus_states.sort_by(|a, b| a.height.cmp(&b.height));
        consensus_states.reverse();
        Ok(consensus_states)
    }

    fn query_consensus_state(
        &self,
        client_id: ClientId,
        consensus_height: ICSHeight,
        query_height: ICSHeight,
    ) -> Result<AnyConsensusState, Error> {
        crate::time!("query_chain_clients");

        let consensus_state = self
            .proven_client_consensus(&client_id, consensus_height, query_height)?
            .0;
        Ok(AnyConsensusState::Tendermint(consensus_state))
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        crate::time!("query_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.client_connections(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        // TODO: add warnings for any identifiers that fail to parse (below).
        //      similar to the parsing in `query_connection_channels`.

        let ids = response
            .connection_paths
            .iter()
            .filter_map(|id| ConnectionId::from_str(id).ok())
            .collect();

        Ok(ids)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        crate::time!("query_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
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

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<ConnectionEnd, Error> {
        async fn do_query_connection(
            chain: &CosmosSdkChain,
            connection_id: &ConnectionId,
            height: ICSHeight,
        ) -> Result<ConnectionEnd, Error> {
            use ibc_proto::ibc::core::connection::v1 as connection;
            use tonic::{metadata::MetadataValue, IntoRequest};

            let mut client =
                connection::query_client::QueryClient::connect(chain.grpc_addr.clone())
                    .await
                    .map_err(|e| Kind::Grpc.context(e))?;

            let mut request = connection::QueryConnectionRequest {
                connection_id: connection_id.to_string(),
            }
            .into_request();

            let height_param = MetadataValue::from_str(&height.revision_height.to_string())
                .map_err(|e| Kind::Grpc.context(e))?;

            request
                .metadata_mut()
                .insert("x-cosmos-block-height", height_param);

            let response = client.connection(request).await.map_err(|e| {
                if e.code() == Code::NotFound {
                    Kind::ConnectionNotFound(connection_id.clone()).into()
                } else {
                    Kind::Grpc.context(e)
                }
            })?;

            match response.into_inner().connection {
                Some(raw_connection) => {
                    let connection_end = raw_connection
                        .try_into()
                        .map_err(|e| Kind::Grpc.context(e))?;

                    Ok(connection_end)
                }
                None => {
                    // When no connection is found, the GRPC call itself should return
                    // the NotFound error code. Nevertheless even if the call is successful,
                    // the connection field may not be present, because in protobuf3
                    // everything is optional.
                    Err(Kind::ConnectionNotFound(connection_id.clone()).into())
                }
            }
        }

        self.block_on(async { do_query_connection(self, connection_id, height).await })
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        crate::time!("query_connection_channels");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.connection_channels(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        // TODO: add warnings for any identifiers that fail to parse (below).
        //  https://github.com/informalsystems/ibc-rs/pull/506#discussion_r555945560

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| IdentifiedChannelEnd::try_from(ch).ok())
            .collect();
        Ok(channels)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        crate::time!("query_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.channels(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| IdentifiedChannelEnd::try_from(ch).ok())
            .collect();
        Ok(channels)
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<ChannelEnd, Error> {
        let res = self.query(
            Path::ChannelEnds(port_id.clone(), channel_id.clone()),
            height,
            false,
        )?;
        let channel_end = ChannelEnd::decode_vec(&res.value).map_err(|e| {
            Kind::Query(format!("port '{}' & channel '{}'", port_id, channel_id)).context(e)
        })?;

        Ok(channel_end)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        crate::time!("query_channel_client_state");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.channel_client_state(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        let client_state: Option<IdentifiedAnyClientState> = response
            .identified_client_state
            .map_or_else(|| None, |proto_cs| proto_cs.try_into().ok());

        Ok(client_state)
    }

    /// Queries the packet commitment hashes associated with a channel.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, ICSHeight), Error> {
        crate::time!("query_packet_commitments");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
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

    /// Queries the unreceived packet sequences associated with a channel.
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        crate::time!("query_unreceived_packets");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let mut response = self
            .block_on(client.unreceived_packets(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        response.sequences.sort_unstable();
        Ok(response.sequences)
    }

    /// Queries the packet acknowledgment hashes associated with a channel.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, ICSHeight), Error> {
        crate::time!("query_packet_acknowledgements");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
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

    /// Queries the unreceived acknowledgements sequences associated with a channel.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        crate::time!("query_unreceived_acknowledgements");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let mut response = self
            .block_on(client.unreceived_acks(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        response.sequences.sort_unstable();
        Ok(response.sequences)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error> {
        crate::time!("query_next_sequence_receive");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(|e| Kind::Grpc.context(e))?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.next_sequence_receive(request))
            .map_err(|e| Kind::Grpc.context(e))?
            .into_inner();

        Ok(Sequence::from(response.next_sequence_receive))
    }

    /// This function queries transactions for events matching certain criteria.
    /// 1. Client Update request - returns a vector with at most one update client event
    /// 2. Packet event request - returns at most one packet event for each sequence specified
    ///    in the request.
    ///    Note - there is no way to format the packet query such that it asks for Tx-es with either
    ///    sequence (the query conditions can only be AND-ed).
    ///    There is a possibility to include "<=" and ">=" conditions but it doesn't work with
    ///    string attributes (sequence is emmitted as a string).
    ///    Therefore, for packets we perform one tx_search for each sequence.
    ///    Alternatively, a single query for all packets could be performed but it would return all
    ///    packets ever sent.
    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("query_txs");

        match request {
            QueryTxRequest::Packet(request) => {
                crate::time!("query_txs: query packet events");

                let mut result: Vec<IbcEvent> = vec![];

                for seq in &request.sequences {
                    // query first (and only) Tx that includes the event specified in the query request
                    let response = self
                        .block_on(self.rpc_client.tx_search(
                            packet_query(&request, *seq),
                            false,
                            1,
                            1, // get only the first Tx matching the query
                            Order::Ascending,
                        ))
                        .map_err(|e| Kind::Grpc.context(e))?;

                    assert!(
                        response.txs.len() <= 1,
                        "packet_from_tx_search_response: unexpected number of txs"
                    );

                    if response.txs.is_empty() {
                        continue;
                    }

                    if let Some(event) = packet_from_tx_search_response(
                        self.id(),
                        &request,
                        *seq,
                        response.txs[0].clone(),
                    ) {
                        result.push(event);
                    }
                }
                Ok(result)
            }

            QueryTxRequest::Client(request) => {
                crate::time!("query_txs: single client update event");

                // query the first Tx that includes the event matching the client request
                // Note: it is possible to have multiple Tx-es for same client and consensus height.
                // In this case it must be true that the client updates were performed with tha
                // same header as the first one, otherwise a subsequent transaction would have
                // failed on chain. Therefore only one Tx is of interest and current API returns
                // the first one.
                let mut response = self
                    .block_on(self.rpc_client.tx_search(
                        header_query(&request),
                        false,
                        1,
                        1, // get only the first Tx matching the query
                        Order::Ascending,
                    ))
                    .map_err(|e| Kind::Grpc.context(e))?;

                if response.txs.is_empty() {
                    return Ok(vec![]);
                }

                // the response must include a single Tx as specified in the query.
                assert!(
                    response.txs.len() <= 1,
                    "packet_from_tx_search_response: unexpected number of txs"
                );

                let tx = response.txs.remove(0);
                let event = update_client_from_tx_search_response(self.id(), &request, tx);

                Ok(event.into_iter().collect())
            }
        }
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

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        let res = self
            .query(Path::Connections(connection_id.clone()), height, true)
            .map_err(|e| Kind::Query("proven connection".into()).context(e))?;
        let connection_end = ConnectionEnd::decode_vec(&res.value)
            .map_err(|e| Kind::Query("proven connection".into()).context(e))?;

        Ok((
            connection_end,
            res.proof.ok_or_else(|| {
                Kind::Query("proven connection".into()).context("empty proof".to_string())
            })?,
        ))
    }

    fn proven_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<(ChannelEnd, MerkleProof), Error> {
        let res = self
            .query(
                Path::ChannelEnds(port_id.clone(), channel_id.clone()),
                height,
                true,
            )
            .map_err(|e| Kind::Query("proven channel".into()).context(e))?;

        let channel_end = ChannelEnd::decode_vec(&res.value)
            .map_err(|e| Kind::Query("proven channel".into()).context(e))?;

        Ok((
            channel_end,
            res.proof.ok_or_else(|| {
                Kind::Query("proven channel".into()).context("empty proof".to_string())
            })?,
        ))
    }

    fn proven_packet(
        &self,
        packet_type: PacketMsgType,
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
        height: ICSHeight,
    ) -> Result<(Vec<u8>, MerkleProof), Error> {
        let data = match packet_type {
            PacketMsgType::Recv => Path::Commitments {
                port_id,
                channel_id,
                sequence,
            },
            PacketMsgType::Ack => Path::Acks {
                port_id,
                channel_id,
                sequence,
            },
            PacketMsgType::TimeoutUnordered => Path::Receipts {
                port_id,
                channel_id,
                sequence,
            },
            PacketMsgType::TimeoutOrdered => Path::SeqRecvs {
                0: port_id,
                1: channel_id,
            },
            PacketMsgType::TimeoutOnClose => Path::Receipts {
                port_id,
                channel_id,
                sequence,
            },
        };

        let res = self
            .query(data, height, true)
            .map_err(|e| Kind::Query(packet_type.to_string()).context(e))?;

        let commitment_proof_bytes = res.proof.ok_or_else(|| {
            Kind::Query(packet_type.to_string()).context("empty proof".to_string())
        })?;

        Ok((res.value, commitment_proof_bytes))
    }

    fn build_client_state(&self, height: ICSHeight) -> Result<Self::ClientState, Error> {
        // Build the client state.
        Ok(ClientState::new(
            self.id().clone(),
            self.config.trust_threshold,
            self.config.trusting_period,
            self.unbonding_period()?,
            self.config.clock_drift,
            height,
            ICSHeight::zero(),
            vec!["upgrade".to_string(), "upgradedIBCState".to_string()],
            AllowUpdate {
                after_expiry: true,
                after_misbehaviour: true,
            },
        )
        .map_err(|e| Kind::BuildClientStateFailure.context(e))?)
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
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
        light_client: &mut dyn LightClient<Self>,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        crate::time!("build_header");

        // Get the light block at target_height from chain.
        let Verified { target, supporting } =
            light_client.header_and_minimal_set(trusted_height, target_height, client_state)?;

        Ok((target, supporting))
    }
}

fn packet_query(request: &QueryPacketEventDataRequest, seq: Sequence) -> Query {
    tendermint_rpc::query::Query::eq(
        format!("{}.packet_src_channel", request.event_id.as_str()),
        request.source_channel_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_src_port", request.event_id.as_str()),
        request.source_port_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_dst_channel", request.event_id.as_str()),
        request.destination_channel_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_dst_port", request.event_id.as_str()),
        request.destination_port_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_sequence", request.event_id.as_str()),
        seq.to_string(),
    )
}

fn header_query(request: &QueryClientEventRequest) -> Query {
    tendermint_rpc::query::Query::eq(
        format!("{}.client_id", request.event_id.as_str()),
        request.client_id.to_string(),
    )
    .and_eq(
        format!("{}.consensus_height", request.event_id.as_str()),
        format!(
            "{}-{}",
            request.consensus_height.revision_number, request.consensus_height.revision_height
        ),
    )
}

// Extract the packet events from the query_txs RPC response. For any given
// packet query, there is at most one Tx matching such query. Moreover, a Tx may
// contain several events, but a single one must match the packet query.
// For example, if we're querying for the packet with sequence 3 and this packet
// was committed in some Tx along with the packet with sequence 4, the response
// will include both packets. For this reason, we iterate all packets in the Tx,
// searching for those that match (which must be a single one).
fn packet_from_tx_search_response(
    chain_id: &ChainId,
    request: &QueryPacketEventDataRequest,
    seq: Sequence,
    response: ResultTx,
) -> Option<IbcEvent> {
    let height = ICSHeight::new(chain_id.version(), u64::from(response.height));
    if request.height != ICSHeight::zero() && height > request.height {
        return None;
    }

    response
        .tx_result
        .events
        .into_iter()
        .filter(|abci_event| abci_event.type_str == request.event_id.as_str())
        .flat_map(|abci_event| ChannelEvents::try_from_tx(&abci_event))
        .find(|event| {
            let packet = match event {
                IbcEvent::SendPacket(send_ev) => Some(&send_ev.packet),
                IbcEvent::WriteAcknowledgement(ack_ev) => Some(&ack_ev.packet),
                _ => None,
            };

            packet.map_or(false, |packet| {
                packet.source_port == request.source_port_id
                    && packet.source_channel == request.source_channel_id
                    && packet.destination_port == request.destination_port_id
                    && packet.destination_channel == request.destination_channel_id
                    && packet.sequence == seq
            })
        })
}

// Extracts from the Tx the update client event for the requested client and height.
// Note: in the Tx, there may have been multiple events, some of them may be
// for update of other clients that are not relevant to the request.
// For example, if we're querying for a transaction that includes the update for client X at
// consensus height H, it is possible that the transaction also includes an update client
// for client Y at consensus height H'. This is the reason the code iterates all event fields in the
// returned Tx to retrieve the relevant ones.
// Returns `None` if no matching event was found.
fn update_client_from_tx_search_response(
    chain_id: &ChainId,
    request: &QueryClientEventRequest,
    response: ResultTx,
) -> Option<IbcEvent> {
    let height = ICSHeight::new(chain_id.version(), u64::from(response.height));
    if request.height != ICSHeight::zero() && height > request.height {
        return None;
    }

    response
        .tx_result
        .events
        .into_iter()
        .filter(|event| event.type_str == request.event_id.as_str())
        .flat_map(|event| ClientEvents::try_from_tx(&event))
        .flat_map(|event| match event {
            IbcEvent::UpdateClient(update) => Some(update),
            _ => None,
        })
        .find(|update| {
            update.common.client_id == request.client_id
                && update.common.consensus_height == request.consensus_height
        })
        .map(IbcEvent::UpdateClient)
}

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
async fn abci_query(
    chain: &CosmosSdkChain,
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

    let proof = response
        .proof
        .map(|p| convert_tm_to_ics_merkle_proof(&p))
        .transpose()
        .map_err(Kind::Ics023)?;

    let response = QueryResponse {
        value: response.value,
        height: response.height,
        proof,
    };

    Ok(response)
}

/// Perform a `broadcast_tx_commit`, and return the corresponding deserialized response data.
async fn broadcast_tx_commit(
    chain: &CosmosSdkChain,
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
async fn query_account(chain: &CosmosSdkChain, address: String) -> Result<BaseAccount, Error> {
    let mut client = ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient::connect(
        chain.grpc_addr.clone(),
    )
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

pub fn tx_result_to_event(
    chain_id: &ChainId,
    response: Response,
) -> Result<Vec<IbcEvent>, anomaly::Error<Kind>> {
    let mut result = vec![];

    // Verify the return codes from check_tx and deliver_tx
    if response.check_tx.code.is_err() {
        return Ok(vec![IbcEvent::ChainError(format!(
            "check_tx reports error: log={:?}",
            response.check_tx.log
        ))]);
    }
    if response.deliver_tx.code.is_err() {
        return Ok(vec![IbcEvent::ChainError(format!(
            "deliver_tx reports error: log={:?}",
            response.deliver_tx.log
        ))]);
    }

    let height = ICSHeight::new(chain_id.version(), u64::from(response.height));
    for event in response.deliver_tx.events {
        if let Some(ibc_ev) = from_tx_response_event(height, &event) {
            result.push(ibc_ev);
        }
    }
    Ok(result)
}

fn encode_to_bech32(address: &str, account_prefix: &str) -> Result<String, Error> {
    let account =
        AccountId::from_str(address).map_err(|_| Kind::InvalidKeyAddress(address.to_string()))?;

    let encoded = bech32::encode(account_prefix, account.to_base32(), Variant::Bech32)
        .map_err(Kind::Bech32Encoding)?;

    Ok(encoded)
}

/// Returns the suffix counter for a CosmosSDK client id.
/// Returns `None` if the client identifier is malformed
/// and the suffix could not be parsed.
pub fn client_id_suffix(client_id: &ClientId) -> Option<u64> {
    client_id
        .as_str()
        .split('-')
        .last()
        .map(|e| e.parse::<u64>().ok())
        .flatten()
}
