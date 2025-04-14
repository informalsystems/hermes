pub mod config;
pub mod util;
pub mod version;

use anyhow::Context;
use futures::{FutureExt, StreamExt, TryStreamExt};
use http::Uri;
use ibc_proto::ics23;
use ibc_relayer_types::applications::ics28_ccv::msgs::ConsumerChain;
use ibc_relayer_types::core::ics02_client;
use ibc_relayer_types::core::ics04_channel;
use pbjson_types;

use ibc_proto::ibc::core::channel::v1::QueryChannelRequest as RawQueryChannelRequest;
use ibc_proto::ibc::core::channel::v1::QueryNextSequenceReceiveRequest as RawQueryNextSequenceReceiveRequest;
use ibc_proto::ibc::core::channel::v1::QueryPacketAcknowledgementRequest as RawQueryPacketAcknowledgementRequest;
use ibc_proto::ibc::core::channel::v1::QueryPacketCommitmentRequest as RawQueryPacketCommitmentRequest;
use ibc_proto::ibc::core::channel::v1::QueryPacketReceiptRequest as RawQueryPacketReceiptRequest;
use ibc_proto::ibc::core::client::v1::QueryClientStateRequest as RawQueryClientStateRequest;
use ibc_proto::ibc::core::client::v1::QueryConsensusStateRequest as RawQueryConsensusStatesRequest;
use ibc_proto::ibc::core::connection::v1::QueryConnectionRequest as RawQueryConnectionRequest;

use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use once_cell::sync::Lazy;
use penumbra_sdk_proto::core::app::v1::AppParametersRequest;
use penumbra_sdk_proto::core::component::ibc::v1::IbcRelay as ProtoIbcRelay;
use penumbra_sdk_proto::DomainType as _;
use penumbra_sdk_transaction::txhash::TransactionId;
use penumbra_sdk_transaction::Transaction;
use prost::Message;
use std::cmp::Ordering;
use std::str::FromStr;
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use tracing::info;

use crate::chain::client::ClientSettings;
use crate::chain::endpoint::ChainStatus;
use crate::chain::requests::*;
use crate::chain::tracking::TrackedMsgs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::consensus_state::AnyConsensusState;
use crate::event::source::{EventSource, TxEventSourceCmd};
use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};
use crate::keyring::KeyRing;
use crate::light_client::tendermint::LightClient as TmLightClient;
use crate::light_client::LightClient;
use crate::util::pretty::{
    PrettyIdentifiedChannel, PrettyIdentifiedClientState, PrettyIdentifiedConnection,
};
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
use ibc_proto::ibc::core::{
    channel::v1::query_client::QueryClient as IbcChannelQueryClient,
    client::v1::query_client::QueryClient as IbcClientQueryClient,
    connection::v1::query_client::QueryClient as IbcConnectionQueryClient,
};
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState as TmClientState;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TmHeader;
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer_types::Height as ICSHeight;
use penumbra_sdk_fee::FeeTier;
use penumbra_sdk_ibc::IbcRelay;
use penumbra_sdk_keys::keys::AddressIndex;
use penumbra_sdk_proto::box_grpc_svc::{self, BoxGrpcService};
use penumbra_sdk_proto::{
    core::app::v1::query_service_client::QueryServiceClient as AppQueryClient,
    custody::v1::{
        custody_service_client::CustodyServiceClient, custody_service_server::CustodyServiceServer,
    },
    view::v1::{
        broadcast_transaction_response::Status as BroadcastStatus,
        view_service_client::ViewServiceClient, view_service_server::ViewServiceServer,
        GasPricesRequest,
    },
};
use penumbra_sdk_view::{ViewClient, ViewServer};
use penumbra_sdk_wallet::plan::Planner;
use signature::rand_core::OsRng;

use tendermint::time::Time as TmTime;
use tendermint_light_client::verifier::types::LightBlock as TmLightBlock;
use tendermint_rpc::{Client as _, HttpClient};
use tokio::runtime::Runtime as TokioRuntime;
use tokio::sync::Mutex;
use tonic::IntoRequest;

use std::path::PathBuf;

use crate::{
    chain::{
        endpoint::{ChainEndpoint, HealthCheck},
        handle::Subscription,
    },
    config::{ChainConfig, Error as ConfigError},
    error::Error,
    keyring::Secp256k1KeyPair,
};

use crate::chain::penumbra::config::PenumbraConfig;

pub struct PenumbraChain {
    config: PenumbraConfig,
    rt: Arc<TokioRuntime>,

    view_client: Mutex<ViewServiceClient<BoxGrpcService>>,
    custody_client: CustodyServiceClient<BoxGrpcService>,

    ibc_client_grpc_client: IbcClientQueryClient<tonic::transport::Channel>,
    ibc_connection_grpc_client: IbcConnectionQueryClient<tonic::transport::Channel>,
    ibc_channel_grpc_client: IbcChannelQueryClient<tonic::transport::Channel>,

    tendermint_rpc_client: HttpClient,
    tendermint_light_client: TmLightClient,

    tx_monitor_cmd: Option<TxEventSourceCmd>,

    unbonding_period: Duration,
}

impl PenumbraChain {
    fn init_event_source(&mut self) -> Result<TxEventSourceCmd, Error> {
        crate::time!(
            "init_event_source",
            {
                "src_chain": self.config().id().to_string(),
            }
        );

        use crate::config::EventSourceMode as Mode;

        let (event_source, monitor_tx) = match &self.config.event_source {
            Mode::Pull {
                interval,
                max_retries,
            } => EventSource::rpc(
                self.config.id.clone(),
                self.tendermint_rpc_client.clone(),
                *interval,
                *max_retries,
                self.rt.clone(),
            ),
            _ => unimplemented!(),
        }
        .map_err(Error::event_source)?;

        thread::spawn(move || event_source.run());

        Ok(monitor_tx)
    }

    fn chain_status(&self) -> Result<tendermint_rpc::endpoint::status::Response, Error> {
        let status = self
            .rt
            .block_on(self.tendermint_rpc_client.status())
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        Ok(status)
    }

    async fn ibc_events_for_penumbratx(
        &self,
        penumbra_tx_id: TransactionId,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let txid = penumbra_tx_id.0.to_vec().try_into().unwrap();
        let tm_tx = self
            .tendermint_rpc_client
            .tx(txid, false)
            .await
            .map_err(|e| {
                tracing::error!("error querying transaction: {}", e);
                Error::temp_penumbra_error(e.to_string())
            })?;

        let height = ICSHeight::new(self.config.id.version(), u64::from(tm_tx.height)).unwrap();
        let events = tm_tx
            .tx_result
            .events
            .iter()
            .filter_map(|ev| {
                if let Ok(ibc_event) = ibc_event_try_from_abci_event(ev) {
                    Some(IbcEventWithHeight::new(ibc_event, height))
                } else {
                    None
                }
            })
            .collect();

        Ok(events)
    }

    async fn query_packets_from_blocks(
        &self,
        request: &QueryPacketEventDataRequest,
    ) -> Result<(Vec<IbcEventWithHeight>, Vec<IbcEventWithHeight>), Error> {
        use crate::chain::cosmos::query::packet_query;

        let mut begin_block_events = vec![];
        let mut end_block_events = vec![];

        for seq in request.sequences.iter().copied() {
            let response = self
                .tendermint_rpc_client
                .block_search(
                    packet_query(request, seq),
                    // We only need the first page
                    1,
                    // There should only be a single match for this query, but due to
                    // the fact that the indexer treat the query as a disjunction over
                    // all events in a block rather than a conjunction over a single event,
                    // we may end up with partial matches and therefore have to account for
                    // that by fetching multiple results and filter it down after the fact.
                    // In the worst case we get N blocks where N is the number of channels,
                    // but 10 seems to work well enough in practice while keeping the response
                    // size, and therefore pressure on the node, fairly low.
                    10,
                    // We could pick either ordering here, since matching blocks may be at pretty
                    // much any height relative to the target blocks, so we went with most recent
                    // blocks first.
                    tendermint_rpc::Order::Descending,
                )
                .await
                .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

            for block in response.blocks.into_iter().map(|response| response.block) {
                let response_height =
                    ICSHeight::new(self.id().version(), u64::from(block.header.height))
                        .map_err(|_| Error::invalid_height_no_source())?;

                if let QueryHeight::Specific(query_height) = request.height.get() {
                    if response_height > query_height {
                        continue;
                    }
                }

                // `query_packet_from_block` retrieves the begin and end block events
                // and filter them to retain only those matching the query
                let (new_begin_block_events, new_end_block_events) =
                    self.query_packet_from_block(request, &[seq], &response_height)?;

                begin_block_events.extend(new_begin_block_events);
                end_block_events.extend(new_end_block_events);
            }
        }

        Ok((begin_block_events, end_block_events))
    }

    pub(super) fn query_packet_from_block(
        &self,
        request: &QueryPacketEventDataRequest,
        seqs: &[Sequence],
        block_height: &ICSHeight,
    ) -> Result<(Vec<IbcEventWithHeight>, Vec<IbcEventWithHeight>), Error> {
        use crate::chain::cosmos::query::tx::filter_matching_event;

        let mut begin_block_events = vec![];
        let mut end_block_events = vec![];

        let tm_height =
            tendermint::block::Height::try_from(block_height.revision_height()).unwrap();

        let response = self
            .rt
            .block_on(self.tendermint_rpc_client.block_results(tm_height))
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        let response_height = ICSHeight::new(self.id().version(), u64::from(response.height))
            .map_err(|_| Error::invalid_height_no_source())?;

        begin_block_events.append(
            &mut response
                .begin_block_events
                .unwrap_or_default()
                .iter()
                .filter_map(|ev| filter_matching_event(ev, request, seqs))
                .map(|ev| IbcEventWithHeight::new(ev, response_height))
                .collect(),
        );

        end_block_events.append(
            &mut response
                .end_block_events
                .unwrap_or_default()
                .iter()
                .filter_map(|ev| filter_matching_event(ev, request, seqs))
                .map(|ev| IbcEventWithHeight::new(ev, response_height))
                .collect(),
        );

        Ok((begin_block_events, end_block_events))
    }

    async fn build_penumbra_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<penumbra_sdk_transaction::Transaction, anyhow::Error> {
        let mut view_client = self.view_client.lock().await.clone();
        let gas_prices = view_client
            .gas_prices(GasPricesRequest {})
            .await
            .unwrap()
            .into_inner()
            .gas_prices
            .expect("gas prices must be available")
            .try_into()
            .unwrap();
        // TODO: should this be a config option?
        let fee_tier = FeeTier::default();

        // use the transaction builder in the custody service to construct a transaction, including
        // each tracked message as an IbcRelay message
        let mut planner = Planner::new(OsRng);

        planner.set_gas_prices(gas_prices).set_fee_tier(fee_tier);

        for msg in tracked_msgs.msgs {
            let raw_ibcrelay_msg = ProtoIbcRelay {
                raw_action: Some(pbjson_types::Any {
                    type_url: msg.type_url.clone(),
                    value: msg.value.clone().into(),
                }),
            };
            let ibc_action =
                IbcRelay::try_from(raw_ibcrelay_msg).expect("failed to convert to IbcRelay");
            planner.ibc_action(ibc_action);
        }

        let plan = planner.plan(&mut view_client, AddressIndex::new(0)).await?;

        penumbra_sdk_wallet::build_transaction(
            self.config.kms_config.spend_key.full_viewing_key(),
            &mut view_client,
            &mut self.custody_client,
            plan,
        )
        .await
    }

    async fn send_messages_in_penumbratx(
        &mut self,
        tracked_msgs: TrackedMsgs,
        wait_for_commit: bool,
    ) -> Result<penumbra_sdk_transaction::txhash::TransactionId, Error> {
        let view_client = self.view_client.lock().await.clone();
        let tx = self.build_penumbra_tx(tracked_msgs).await.map_err(|e| {
            tracing::error!("error building penumbra transaction: {}", e);
            Error::temp_penumbra_error(e.to_string())
        })?;

        let penumbra_txid = self
            .submit_transaction(tx, wait_for_commit, &mut view_client.clone())
            .await
            .map_err(|e| {
                tracing::error!("error submitting transaction: {}", e);
                Error::temp_penumbra_error(e.to_string())
            })?;

        // wait for two blocks of confirmation to be sure that the potentially load-balanced endpoints are synced
        if wait_for_commit {
            let current_height = self
                .tendermint_rpc_client
                .status()
                .await
                .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?
                .sync_info
                .latest_block_height
                .value();
            let mut last_height = current_height;

            while last_height - current_height < 2 {
                thread::sleep(Duration::from_secs(1));
                last_height = self
                    .tendermint_rpc_client
                    .status()
                    .await
                    .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?
                    .sync_info
                    .latest_block_height
                    .value();
            }
        }

        Ok(penumbra_txid)
    }

    async fn submit_transaction(
        &mut self,
        transaction: Transaction,
        wait_for_commit: bool,
        view_client: &mut ViewServiceClient<BoxGrpcService>,
    ) -> anyhow::Result<TransactionId> {
        info!("broadcasting penumbra transaction and awaiting confirmation...");
        let mut rsp =
            ViewClient::broadcast_transaction(view_client, transaction, wait_for_commit).await?;

        let id = (async move {
            while let Some(rsp) = rsp.try_next().await? {
                match rsp.status {
                    Some(status) => match status {
                        BroadcastStatus::BroadcastSuccess(bs) => {
                            if !wait_for_commit {
                                return bs.id.expect("detected transaction missing id").try_into();
                            }
                        }
                        BroadcastStatus::Confirmed(c) => {
                            let id = c.id.expect("detected transaction missing id").try_into()?;
                            info!(id = %id, "penumbra transaction confirmed");
                            return Ok(id);
                        }
                    },
                    None => {
                        // No status is unexpected behavior
                        return Err(anyhow::anyhow!(
                            "empty BroadcastTransactionResponse message"
                        ));
                    }
                }
            }

            Err(anyhow::anyhow!(
                "should have received BroadcastTransaction status or error"
            ))
        }
        .boxed())
        .await
        .map_err(|e| {
            tracing::error!("error awaiting transaction broadcast: {}", e);
            e
        })
        .context("broadcast_transaction failed")?;

        Ok(id)
    }

    async fn query_balance(
        &self,
        address_index: AddressIndex,
        denom: &str,
    ) -> Result<crate::account::Balance, anyhow::Error> {
        let mut view_client = self.view_client.lock().await.clone();
        let assets = ViewClient::assets(&mut view_client).await?;
        let asset_id = assets
            .get_unit(denom)
            .ok_or_else(|| anyhow::anyhow!("denom not found"))?
            .id();

        let balances =
            ViewClient::balances(&mut view_client, address_index, Some(asset_id)).await?;

        for (id, amount) in balances {
            if id != asset_id {
                continue; // should never happen
            }

            return Ok(crate::account::Balance {
                amount: amount.to_string(),
                denom: denom.to_string(),
            });
        }

        Err(anyhow::anyhow!("denom not found"))
    }
}

impl ChainEndpoint for PenumbraChain {
    type LightBlock = TmLightBlock;
    type Header = TmHeader;
    type ConsensusState = TmConsensusState;
    type ClientState = TmClientState;
    type Time = TmTime;
    // Note: this is a placeholder, we won't actually use it.
    type SigningKeyPair = Secp256k1KeyPair;

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn config(&self) -> ChainConfig {
        ChainConfig::Penumbra(self.config.clone())
    }

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let ChainConfig::Penumbra(config) = config else {
            return Err(Error::config(ConfigError::wrong_type()));
        };

        let rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;

        let node_info = rt.block_on(fetch_node_info(&rpc_client, &config))?;

        let fvk = config.kms_config.spend_key.full_viewing_key();

        // Identify filepath for storing Penumbra view database locally.
        // The directory might not be specified, in which case we'll preserve None,
        // which causes the ViewServiceClient to use an in-memory database.
        let view_file: Option<String> = match config.view_service_storage_dir {
            Some(ref dir_string) => {
                let p = PathBuf::from(dir_string)
                    .join("relayer-view.sqlite")
                    .to_str()
                    .ok_or_else(|| Error::temp_penumbra_error("Non-UTF8 view path".to_owned()))?
                    .to_owned();
                tracing::info!("using view database at {}", p);
                Some(p)
            }
            None => {
                tracing::warn!("using in-memory view database for penumbra; consider setting 'view_service_storage_dir'");
                None
            }
        };

        // No support for custom registry.json files in Hermes yet.
        let registry_path: Option<String> = None;
        let svc = rt
            .block_on(ViewServer::load_or_initialize(
                view_file,
                registry_path,
                fvk,
                config.grpc_addr.clone().into(),
            ))
            .map_err(|e| Error::temp_penumbra_error(e.to_string()))?;

        let svc = ViewServiceServer::new(svc);
        let mut view_client = ViewServiceClient::new(box_grpc_svc::local(svc));

        let soft_kms = penumbra_sdk_custody::soft_kms::SoftKms::new(config.kms_config.clone());
        let custody_svc = CustodyServiceServer::new(soft_kms);
        let custody_client = CustodyServiceClient::new(box_grpc_svc::local(custody_svc));

        let grpc_addr = Uri::from_str(&config.grpc_addr.to_string())
            .map_err(|e| Error::invalid_uri(config.grpc_addr.to_string(), e))?;

        let mut app_query = rt
            .block_on(AppQueryClient::connect(grpc_addr.clone()))
            .map_err(Error::grpc_transport)?;

        let app_parameters = rt
            .block_on(app_query.app_parameters(tonic::Request::new(AppParametersRequest {})))
            .map_err(|e| Error::grpc_status(e, "app_parameters query".to_owned()))?
            .into_inner();

        let unbonding_delay = app_parameters
            .app_parameters
            .expect("should have app parameters")
            .stake_params
            .expect("should have stake parameters")
            .unbonding_delay;

        // here we assume roughly 5s block time, which is not part of consensus but should be
        // roughly correct. it would really be better if the ibc protocol gave the client's
        // trusting period in terms of blocks instead of duration.
        let unbonding_period = Duration::from_secs(unbonding_delay * 5);

        tracing::info!("starting view service sync");

        let sync_height = rt
            .block_on(async {
                let mut stream = ViewClient::status_stream(&mut view_client).await?;
                let mut sync_height = 0u64;
                while let Some(status) = stream.next().await.transpose()? {
                    sync_height = status.full_sync_height;
                }
                Ok(sync_height)
            })
            .map_err(|e: anyhow::Error| Error::temp_penumbra_error(e.to_string()))?;

        tracing::info!(?sync_height, "view service sync complete");

        let ibc_client_grpc_client = rt
            .block_on(IbcClientQueryClient::connect(grpc_addr.clone()))
            .map_err(Error::grpc_transport)?;
        let ibc_connection_grpc_client = rt
            .block_on(IbcConnectionQueryClient::connect(grpc_addr.clone()))
            .map_err(Error::grpc_transport)?;
        let ibc_channel_grpc_client = rt
            .block_on(IbcChannelQueryClient::connect(grpc_addr.clone()))
            .map_err(Error::grpc_transport)?;

        let tendermint_light_client = TmLightClient::from_penumbra_config(&config, node_info.id)?;

        tracing::info!("ibc grpc query clients connected");

        Ok(Self {
            config,
            rt,
            view_client: Mutex::new(view_client.clone()),
            custody_client,
            tendermint_rpc_client: rpc_client,
            tendermint_light_client,
            tx_monitor_cmd: None,

            ibc_client_grpc_client,
            ibc_connection_grpc_client,
            ibc_channel_grpc_client,

            unbonding_period,
        })
    }

    fn shutdown(self) -> Result<(), Error> {
        if let Some(monitor_tx) = self.tx_monitor_cmd {
            monitor_tx.shutdown().map_err(Error::event_source)?;
        }

        Ok(())
    }

    fn health_check(&mut self) -> Result<HealthCheck, Error> {
        let mut view_client = self.rt.block_on(self.view_client.lock()).clone();
        let catching_up = self
            .rt
            .block_on(async {
                let status = ViewClient::status(&mut view_client).await?;
                Ok(status.catching_up)
            })
            .map_err(|e: anyhow::Error| Error::temp_penumbra_error(e.to_string()))?;

        if catching_up {
            Ok(HealthCheck::Unhealthy(Box::new(
                Error::temp_penumbra_error(
                    anyhow::anyhow!("view service is not synced").to_string(),
                ),
            )))
        } else {
            Ok(HealthCheck::Healthy)
        }
    }

    fn subscribe(&mut self) -> Result<Subscription, Error> {
        let tx_monitor_cmd = match &self.tx_monitor_cmd {
            Some(tx_monitor_cmd) => tx_monitor_cmd,
            None => {
                let tx_monitor_cmd = self.init_event_source()?;
                self.tx_monitor_cmd = Some(tx_monitor_cmd);
                self.tx_monitor_cmd.as_ref().unwrap()
            }
        };

        let subscription = tx_monitor_cmd.subscribe().map_err(Error::event_source)?;
        Ok(subscription)
    }

    fn keybase(&self) -> &KeyRing<Self::SigningKeyPair> {
        unimplemented!("no key storage support for penumbra")
    }

    fn keybase_mut(&mut self) -> &mut KeyRing<Self::SigningKeyPair> {
        unimplemented!("no key storage support for penumbra")
    }

    fn get_signer(&self) -> Result<ibc_relayer_types::signer::Signer, Error> {
        Ok(ibc_relayer_types::signer::Signer::dummy())
    }

    fn get_key(&self) -> Result<Self::SigningKeyPair, Error> {
        Err(Error::temp_penumbra_error(
            "TODO: telemetry should not require keyring access".to_string(),
        ))
    }

    fn version_specs(&self) -> Result<crate::chain::version::Specs, Error> {
        // We don't have to do version negotiation, we support the smallest
        // possible feature set.
        Ok(crate::chain::version::Specs::Penumbra(version::Specs {
            penumbra: None,
            consensus: None,
        }))
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let runtime = self.rt.clone();
        let txid = runtime.block_on(self.send_messages_in_penumbratx(tracked_msgs, true))?;
        let events = runtime.block_on(self.ibc_events_for_penumbratx(txid))?;

        Ok(events)
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        let runtime = self.rt.clone();
        let penumbra_tx = runtime
            .block_on(self.build_penumbra_tx(tracked_msgs.clone()))
            .map_err(|e| {
                tracing::error!("error building penumbra transaction: {}", e);
                Error::temp_penumbra_error(e.to_string())
            })?;

        let tx_bytes = penumbra_tx.encode_to_vec();

        let res = runtime
            .block_on(self.tendermint_rpc_client.broadcast_tx_sync(tx_bytes))
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        Ok(vec![res])
    }

    fn verify_header(
        &mut self,
        trusted: ibc_relayer_types::Height,
        target: ibc_relayer_types::Height,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        crate::time!(
            "verify_header",
            {
                "src_chain": self.config().id().to_string(),
            }
        );

        let now = self.chain_status()?.sync_info.latest_block_time;

        self.tendermint_light_client
            .verify(trusted, target, client_state, now)
            .map(|v| v.target)
    }

    fn check_misbehaviour(
        &mut self,
        update: &ibc_relayer_types::core::ics02_client::events::UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<crate::misbehaviour::MisbehaviourEvidence>, Error> {
        crate::time!(
            "check_misbehaviour",
            {
                "src_chain": self.config().id().to_string(),
            }
        );

        let now = self.chain_status()?.sync_info.latest_block_time;

        self.tendermint_light_client
            .detect_misbehaviour(update, client_state, now)
    }

    fn query_balance(
        &self,
        _key_name: Option<&str>,
        denom: Option<&str>,
    ) -> Result<crate::account::Balance, Error> {
        let denom = denom.unwrap_or("upenumbra");

        self.rt
            .block_on(self.query_balance(AddressIndex::new(0), denom))
            .map_err(|e| Error::temp_penumbra_error(e.to_string()))
    }

    fn query_all_balances(
        &self,
        _key_name: Option<&str>,
    ) -> Result<Vec<crate::account::Balance>, Error> {
        unimplemented!("cannot query balance of a shielded chain >:}}")
    }

    fn query_denom_trace(&self, _hash: String) -> Result<crate::denom::DenomTrace, Error> {
        todo!("penumbra doesn't support denom trace querying yet")
    }

    fn query_commitment_prefix(
        &self,
    ) -> Result<ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix, Error>
    {
        // This is hardcoded for now.
        Ok(b"ibc-data".to_vec().try_into().unwrap())
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        crate::time!(
            "query_application_status",
            {
                "src_chain": self.config().id().to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_application_status");

        // We cannot rely on `/status` endpoint to provide details about the latest block.
        // Instead, we need to pull block height via `/abci_info` and then fetch block
        // metadata at the given height via `/blockchain` endpoint.
        let abci_info = self
            .rt
            .block_on(self.tendermint_rpc_client.abci_info())
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        // Query `/header` endpoint to pull the latest block that the application committed.
        let response = self
            .rt
            .block_on(
                self.tendermint_rpc_client
                    .header(abci_info.last_block_height),
            )
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        let height = ICSHeight::new(
            ChainId::chain_version(response.header.chain_id.as_str()),
            u64::from(abci_info.last_block_height),
        )
        .map_err(|_| Error::invalid_height_no_source())?;

        let timestamp = response.header.time.into();
        Ok(ChainStatus { height, timestamp })
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        crate::time!(
            "query_clients",
            {
                "src_chain": self.config().id().to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_clients");

        let mut client = self.ibc_client_grpc_client.clone();

        let request = tonic::Request::new(request.into());
        let response = self
            .rt
            .block_on(client.client_states(request))
            .map_err(|e| Error::grpc_status(e, "query_clients".to_owned()))?
            .into_inner();

        // Deserialize into domain type
        let mut clients: Vec<IdentifiedAnyClientState> = response
            .client_states
            .into_iter()
            .filter_map(|cs| {
                IdentifiedAnyClientState::try_from(cs.clone())
                    .map_err(|e| {
                        tracing::warn!(
                            "failed to parse client state {}. Error: {}",
                            PrettyIdentifiedClientState(&cs),
                            e
                        )
                    })
                    .ok()
            })
            .collect();

        // Sort by client identifier counter
        clients.sort_by_cached_key(|c| client_id_suffix(&c.client_id).unwrap_or(0));

        Ok(clients)
    }

    fn query_client_state(
        &self,
        req: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        crate::telemetry!(query, self.id(), "query_client_state");
        let mut client = self.ibc_client_grpc_client.clone();

        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };

        let proto_request: RawQueryClientStateRequest = req.into();
        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().expect("valid height"));

        // TODO(erwan): for now, playing a bit fast-and-loose with the error handling.
        let response = self
            .rt
            .block_on(client.client_state(request))
            .map_err(|e| Error::other(e.to_string()))?
            .into_inner();

        let raw_client_state = response
            .client_state
            .ok_or_else(Error::empty_response_value)?;
        let raw_proof_bytes = response.proof;
        // let maybe_proof_height = response.proof_height;

        let client_state: AnyClientState = raw_client_state
            .try_into()
            .map_err(|e: ics02_client::error::Error| Error::other(e.to_string()))?;

        match include_proof {
            IncludeProof::Yes => {
                // First, check that the raw proof is not empty.
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                // Only then, attempt to deserialize the proof.
                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((client_state, Some(proof)))
            }
            IncludeProof::No => Ok((client_state, None)),
        }
    }

    fn query_consensus_state(
        &self,
        req: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        crate::telemetry!(query, self.id(), "query_consensus_state");
        let mut client = self.ibc_client_grpc_client.clone();

        let height: String = match req.query_height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };

        let mut proto_request: RawQueryConsensusStatesRequest = req.into();
        // TODO(erwan): the connection handshake fails when we request the latest height.
        // This is ostensibly a bug in hermes, in particular when we build the handshake message.
        // However, for now, we can work around this by always overriding the flag to `false`.
        proto_request.latest_height = false;

        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().unwrap());
        let response = self
            .rt
            .block_on(client.consensus_state(request))
            .map_err(|e| Error::other(e.to_string()))?
            .into_inner();

        let raw_consensus_state = response
            .consensus_state
            .ok_or_else(Error::empty_response_value)?;
        let raw_proof_bytes = response.proof;

        let consensus_state: AnyConsensusState = raw_consensus_state
            .try_into()
            .map_err(|e: ics02_client::error::Error| Error::other(e.to_string()))?;

        if !matches!(consensus_state, AnyConsensusState::Tendermint(_)) {
            return Err(Error::consensus_state_type_mismatch(
                ClientType::Tendermint,
                consensus_state.client_type(),
            ));
        }

        match include_proof {
            IncludeProof::No => Ok((consensus_state, None)),
            IncludeProof::Yes => {
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((consensus_state, Some(proof)))
            }
        }
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<ibc_relayer_types::Height>, Error> {
        let mut client = self.ibc_client_grpc_client.clone();

        let req = ibc_proto::ibc::core::client::v1::QueryConsensusStateHeightsRequest {
            client_id: request.client_id.to_string(),
            pagination: Default::default(),
        };

        let response = self
            .rt
            .block_on(client.consensus_state_heights(req))
            .map_err(|e| Error::grpc_status(e, "query_consensus_state_heights".to_owned()))?
            .into_inner();

        let heights = response
            .consensus_state_heights
            .into_iter()
            .filter_map(|h| ICSHeight::new(h.revision_number, h.revision_height).ok())
            .collect();
        Ok(heights)
    }

    fn query_upgraded_client_state(
        &self,
        _request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        todo!("need to implement corresponding state query in penumbra")
    }

    fn query_upgraded_consensus_state(
        &self,
        _request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        todo!("need to implement corresponding state query in penumbra")
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        crate::time!(
            "query_connections",
            {
                "src_chain": self.config().id().to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_connections");

        let mut client = self.ibc_connection_grpc_client.clone();

        let request = tonic::Request::new(request.into());

        let response = self
            .rt
            .block_on(client.connections(request))
            .map_err(|e| Error::grpc_status(e, "query_connections".to_owned()))?
            .into_inner();

        let connections = response
            .connections
            .into_iter()
            .filter_map(|co| {
                IdentifiedConnectionEnd::try_from(co.clone())
                    .map_err(|e| {
                        tracing::warn!(
                            "connection with ID {} failed parsing. Error: {}",
                            PrettyIdentifiedConnection(&co),
                            e
                        )
                    })
                    .ok()
            })
            .collect();

        Ok(connections)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ibc_relayer_types::core::ics24_host::identifier::ConnectionId>, Error> {
        crate::time!(
            "query_client_connections",
            {
                "src_chain": self.config().id().to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_client_connections");

        let connections = self.query_connections(QueryConnectionsRequest {
            pagination: Default::default(),
        })?;

        let mut client_conns = vec![];
        for connection in connections {
            if connection
                .connection_end
                .client_id_matches(&request.client_id)
            {
                client_conns.push(connection.connection_id);
            }
        }

        Ok(client_conns)
    }

    fn query_connection(
        &self,
        req: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        crate::telemetry!(query, self.id(), "query_connection");
        let mut client = self.ibc_connection_grpc_client.clone();

        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };
        let connection_id = req.connection_id.clone();

        let proto_request: RawQueryConnectionRequest = req.into();
        let mut request = proto_request.into_request();

        request
            .metadata_mut()
            .insert("height", height.parse().unwrap());

        let response = self.rt.block_on(client.connection(request)).map_err(|e| {
            if e.code() == tonic::Code::NotFound {
                Error::connection_not_found(connection_id.clone())
            } else {
                Error::grpc_status(e, "query_connection".to_owned())
            }
        })?;

        let resp = response.into_inner();
        let connection_end: ConnectionEnd = match resp.connection {
            Some(raw_connection) => raw_connection.try_into().map_err(Error::ics03)?,
            None => {
                // When no connection is found, the GRPC call itself should return
                // the NotFound error code. Nevertheless even if the call is successful,
                // the connection field may not be present, because in protobuf3
                // everything is optional.
                return Err(Error::connection_not_found(connection_id));
            }
        };

        match include_proof {
            IncludeProof::Yes => Ok((connection_end, Some(decode_merkle_proof(resp.proof)?))),
            IncludeProof::No => Ok((connection_end, None)),
        }
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .rt
            .block_on(client.connection_channels(request))
            .map_err(|e| Error::grpc_status(e, "query_connection_channels".to_owned()))?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| {
                IdentifiedChannelEnd::try_from(ch.clone())
                    .map_err(|e| {
                        tracing::warn!(
                            "channel with ID {} failed parsing. Error: {}",
                            PrettyIdentifiedChannel(&ch),
                            e
                        )
                    })
                    .ok()
            })
            .collect();
        Ok(channels)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .rt
            .block_on(client.channels(request))
            .map_err(|e| Error::grpc_status(e, "query_channels".to_owned()))?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| {
                IdentifiedChannelEnd::try_from(ch.clone())
                    .map_err(|e| {
                        tracing::warn!(
                            "channel with ID {} failed parsing. Error: {}",
                            PrettyIdentifiedChannel(&ch),
                            e
                        );
                    })
                    .ok()
            })
            .collect();

        Ok(channels)
    }

    /// identifier. A proof can optionally be returned along with the result.
    fn query_channel(
        &self,
        req: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();

        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };

        let proto_request: RawQueryChannelRequest = req.into();
        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().unwrap());

        let response = self
            .rt
            .block_on(client.channel(request))
            .map_err(|e| Error::grpc_status(e, "query_channel".to_owned()))?
            .into_inner();

        let channel = response.channel.ok_or_else(Error::empty_response_value)?;
        let channel_end: ChannelEnd = channel
            .try_into()
            .map_err(|e: ics04_channel::error::Error| Error::other(e.to_string()))?;

        let raw_proof_bytes = response.proof;

        match include_proof {
            IncludeProof::No => Ok((channel_end, None)),
            IncludeProof::Yes => {
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((channel_end, Some(proof)))
            }
        }
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .rt
            .block_on(client.channel_client_state(request))
            .map_err(|e| Error::grpc_status(e, "query_channel_client_state".to_owned()))?
            .into_inner();

        let client_state: Option<IdentifiedAnyClientState> = response
            .identified_client_state
            .map_or_else(|| None, |proto_cs| proto_cs.try_into().ok());

        Ok(client_state)
    }

    fn query_packet_commitment(
        &self,
        req: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        crate::telemetry!(query, self.id(), "query_packet_commitment");
        let mut client = self.ibc_channel_grpc_client.clone();

        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };
        let proto_request: RawQueryPacketCommitmentRequest = req.into();

        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().unwrap());

        let response = self
            .rt
            .block_on(client.packet_commitment(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_commitment".to_owned()))?
            .into_inner();

        let packet_commitment = response.commitment;
        let raw_proof_bytes = response.proof;

        match include_proof {
            IncludeProof::No => Ok((packet_commitment, None)),
            IncludeProof::Yes => {
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((packet_commitment, Some(proof)))
            }
        }
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ibc_relayer_types::Height), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .rt
            .block_on(client.packet_commitments(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_commitments".to_owned()))?
            .into_inner();

        let mut commitment_sequences: Vec<Sequence> = response
            .commitments
            .into_iter()
            .map(|v| v.sequence.into())
            .collect();
        commitment_sequences.sort_unstable();

        let height = response
            .height
            .and_then(|raw_height| raw_height.try_into().ok())
            .ok_or_else(|| Error::grpc_response_param("height".to_string()))?;

        Ok((commitment_sequences, height))
    }

    fn query_packet_receipt(
        &self,
        req: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
        // What a strange API -erwan.
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        crate::telemetry!(query, self.id(), "query_packet_receipt");
        let mut client = self.ibc_channel_grpc_client.clone();
        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };
        let port_id = req.port_id.clone();
        let channel_id = req.channel_id.clone();
        let sequence = req.sequence;

        let proto_request: RawQueryPacketReceiptRequest = req.into();

        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().expect("valid ascii"));

        let response = self
            .rt
            .block_on(client.packet_receipt(request))
            .map_err(|e| {
                if e.code() == tonic::Code::NotFound {
                    Error::other(format!(
                        "packet receipt not found for port_id: {}, channel_id: {}, sequence: {}",
                        port_id, channel_id, sequence
                    ))
                } else {
                    Error::grpc_status(e, "query_packet_receipt".to_owned())
                }
            })?
            .into_inner();

        let raw_proof_bytes = response.proof;

        match include_proof {
            IncludeProof::No => Ok((vec![response.received.into()], None)),
            IncludeProof::Yes => {
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((vec![response.received.into()], Some(proof)))
            }
        }
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();

        let request = tonic::Request::new(request.into());

        let mut response = self
            .rt
            .block_on(client.unreceived_packets(request))
            .map_err(|e| Error::grpc_status(e, "query_unreceived_packets".to_owned()))?
            .into_inner();

        response.sequences.sort_unstable();
        Ok(response
            .sequences
            .into_iter()
            .map(|seq| seq.into())
            .collect())
    }

    fn query_packet_acknowledgement(
        &self,
        req: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
        // TODO(erwan): This API should change. Why are we thrashing raw bytes around?
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        crate::telemetry!(query, self.id(), "query_packet_acknowledgement");
        let mut client = self.ibc_channel_grpc_client.clone();

        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };

        let proto_request: RawQueryPacketAcknowledgementRequest = req.into();
        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().unwrap());

        let response = self
            .rt
            .block_on(client.packet_acknowledgement(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_acknowledgement".to_owned()))?
            .into_inner();

        let raw_ack = response.acknowledgement;
        let raw_proof_bytes = response.proof;
        match include_proof {
            IncludeProof::No => Ok((raw_ack, None)),
            IncludeProof::Yes => {
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((raw_ack, Some(proof)))
            }
        }
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ibc_relayer_types::Height), Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let response = self
            .rt
            .block_on(client.packet_acknowledgements(request))
            .map_err(|e| Error::grpc_status(e, "query_packet_acknowledgements".to_owned()))?
            .into_inner();

        let acks_sequences = response
            .acknowledgements
            .into_iter()
            .map(|v| v.sequence.into())
            .collect();

        let height = response
            .height
            .and_then(|raw_height| raw_height.try_into().ok())
            .ok_or_else(|| Error::grpc_response_param("height".to_string()))?;

        Ok((acks_sequences, height))
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        let mut client = self.ibc_channel_grpc_client.clone();
        let request = tonic::Request::new(request.into());

        let mut response = self
            .rt
            .block_on(client.unreceived_acks(request))
            .map_err(|e| Error::grpc_status(e, "query_unreceived_acknowledgements".to_owned()))?
            .into_inner();

        response.sequences.sort_unstable();
        Ok(response
            .sequences
            .into_iter()
            .map(|seq| seq.into())
            .collect())
    }

    fn query_next_sequence_receive(
        &self,
        req: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        crate::time!(
            "query_next_sequence_receive",
            {
                "src_chain": self.config().id().to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_next_sequence_receive");
        let mut client = self.ibc_channel_grpc_client.clone();

        let height = match req.height {
            QueryHeight::Latest => 0.to_string(),
            QueryHeight::Specific(h) => h.to_string(),
        };

        let proto_request: RawQueryNextSequenceReceiveRequest = req.into();
        let mut request = proto_request.into_request();
        request
            .metadata_mut()
            .insert("height", height.parse().unwrap());

        let response = self
            .rt
            .block_on(client.next_sequence_receive(request))
            .map_err(|e| Error::grpc_status(e, "query_next_sequence_receive".to_owned()))?
            .into_inner();

        // TODO(erwan): previously, there was a comment explaining that we expect
        // a u64 encoded in big-endian in the ABCI query branch. Now that we use
        // gRPC for this query, we shouldn't have to worry about that (this also match previous behavior
        // when a proof is *not* requested). Nevertheless. I will keep the comment here for now:
        // ```
        // Note: We expect the return to be a u64 encoded in big-endian. Refer to ibc-go:
        // https://github.com/cosmos/ibc-go/blob/25767f6bdb5bab2c2a116b41d92d753c93e18121/modules/core/04-channel/client/utils/utils.go#L191
        // ```
        let next_seq: Sequence = response.next_sequence_receive.into();
        let raw_proof_bytes = response.proof;

        match include_proof {
            IncludeProof::Yes => {
                if raw_proof_bytes.is_empty() {
                    return Err(Error::empty_response_proof());
                }

                let raw_proof = RawMerkleProof::decode(raw_proof_bytes.as_ref())
                    .map_err(|e| Error::other(e.to_string()))?;

                let proof = raw_proof.into();

                Ok((next_seq, Some(proof)))
            }
            IncludeProof::No => Ok((next_seq, None)),
        }
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        use crate::chain::cosmos::query::tx::query_txs;

        self.rt.block_on(query_txs(
            self.id(),
            &self.tendermint_rpc_client,
            &self.config.rpc_addr,
            request,
        ))
    }

    fn query_packet_events(
        &self,
        mut request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        use crate::chain::cosmos::query::tx::{query_packets_from_block, query_packets_from_txs};

        match request.height {
            // Usage note: `Qualified::Equal` is currently only used in the call hierarchy involving
            // the CLI methods, namely the CLI for `tx packet-recv` and `tx packet-ack` when the
            // user passes the flag `packet-data-query-height`.
            Qualified::Equal(_) => self.rt.block_on(query_packets_from_block(
                self.id(),
                &self.tendermint_rpc_client,
                &self.config.rpc_addr,
                &request,
            )),
            Qualified::SmallerEqual(_) => {
                let tx_events = self.rt.block_on(query_packets_from_txs(
                    self.id(),
                    &self.tendermint_rpc_client,
                    &self.config.rpc_addr,
                    &request,
                ))?;

                let recvd_sequences: Vec<_> = tx_events
                    .iter()
                    .filter_map(|eh| eh.event.packet().map(|p| p.sequence))
                    .collect();

                request
                    .sequences
                    .retain(|seq| !recvd_sequences.contains(seq));

                let (start_block_events, end_block_events) = if !request.sequences.is_empty() {
                    self.rt.block_on(self.query_packets_from_blocks(&request))?
                } else {
                    Default::default()
                };

                // Events should be ordered in the following fashion,
                // for any two blocks b1, b2 at height h1, h2 with h1 < h2:
                // b1.start_block_events
                // b1.tx_events
                // b1.end_block_events
                // b2.start_block_events
                // b2.tx_events
                // b2.end_block_events
                //
                // As of now, we just sort them by sequence number which should
                // yield a similar result and will revisit this approach in the future.
                let mut events = vec![];
                events.extend(start_block_events);
                events.extend(tx_events);
                events.extend(end_block_events);

                sort_events_by_sequence(&mut events);

                Ok(events)
            }
        }
    }

    fn query_host_consensus_state(
        &self,
        _request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        todo!("need to implement corresponding state query on penumbra")
    }

    fn build_client_state(
        &self,
        height: ibc_relayer_types::Height,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        use ibc_relayer_types::clients::ics07_tendermint::client_state::AllowUpdate;
        let ClientSettings::Tendermint(settings) = settings;
        let trusting_period_default = 2 * self.unbonding_period / 3;
        let trusting_period = settings.trusting_period.unwrap_or(trusting_period_default);

        let proof_specs = IBC_PROOF_SPECS.clone();

        Self::ClientState::new(
            self.id().clone(),
            settings.trust_threshold,
            trusting_period,
            self.unbonding_period,
            settings.max_clock_drift,
            height,
            proof_specs.into(),
            vec!["upgrade".to_string(), "upgradedIBCState".to_string()],
            AllowUpdate {
                after_expiry: true,
                after_misbehaviour: true,
            },
        )
        .map_err(Error::ics07)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        Ok(Self::ConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &mut self,
        trusted_height: ibc_relayer_types::Height,
        target_height: ibc_relayer_types::Height,
        client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        use crate::light_client::Verified;

        let now = self.chain_status()?.sync_info.latest_block_time;

        let Verified { target, supporting } = self.tendermint_light_client.header_and_minimal_set(
            trusted_height,
            target_height,
            client_state,
            now,
        )?;

        Ok((target, supporting))
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        _channel_id: &ibc_relayer_types::core::ics24_host::identifier::ChannelId,
        _port_id: &ibc_relayer_types::core::ics24_host::identifier::PortId,
        _counterparty_payee: &ibc_relayer_types::signer::Signer,
    ) -> Result<(), Error> {
        // the payee is an optional payee to which reverse and timeout relayer packet
        // fees will be paid out.
        todo!("currently unimplemented in penumbra")
    }

    fn cross_chain_query(
        &self,
        _requests: Vec<CrossChainQueryRequest>,
    ) -> Result<
        Vec<ibc_relayer_types::applications::ics31_icq::response::CrossChainQueryResponse>,
        Error,
    > {
        // https://github.com/cosmos/ibc/blob/main/spec/app/ics-031-crosschain-queries/README.md
        todo!("not currently implemented in penumbra")
    }

    fn query_incentivized_packet(
        &self,
        _request: ibc_proto::ibc::apps::fee::v1::QueryIncentivizedPacketRequest,
    ) -> Result<ibc_proto::ibc::apps::fee::v1::QueryIncentivizedPacketResponse, Error> {
        // https://buf.build/cosmos/ibc/docs/e769eb46d1e742e8b0368510479161df:ibc.applications.fee.v1#ibc.applications.fee.v1.Query.IncentivizedPackets
        unimplemented!("not implemented in penumbra")
    }

    fn query_consumer_chains(&self) -> Result<Vec<ConsumerChain>, Error> {
        unimplemented!("not currently implemented in penumbra")
    }

    fn query_upgrade(
        &self,
        _request: ibc_proto::ibc::core::channel::v1::QueryUpgradeRequest,
        _height: ibc_relayer_types::core::ics02_client::height::Height,
        _include_proof: IncludeProof,
    ) -> Result<
        (
            ibc_relayer_types::core::ics04_channel::upgrade::Upgrade,
            Option<MerkleProof>,
        ),
        Error,
    > {
        unimplemented!("not currently implemented in penumbra")
    }

    fn query_upgrade_error(
        &self,
        _request: ibc_proto::ibc::core::channel::v1::QueryUpgradeErrorRequest,
        _height: ibc_relayer_types::core::ics02_client::height::Height,
        _include_proof: IncludeProof,
    ) -> Result<
        (
            ibc_relayer_types::core::ics04_channel::upgrade::ErrorReceipt,
            Option<MerkleProof>,
        ),
        Error,
    > {
        unimplemented!("not currently implemented in penumbra")
    }

    fn query_ccv_consumer_id(
        &self,
        _client_id: ClientId,
    ) -> Result<ibc_relayer_types::applications::ics28_ccv::msgs::ConsumerId, Error> {
        unimplemented!("not currently implemented in penumbra")
    }
}

/// Returns the suffix counter for a CosmosSDK client id.
/// Returns `None` if the client identifier is malformed
/// and the suffix could not be parsed.
fn client_id_suffix(client_id: &ClientId) -> Option<u64> {
    client_id
        .as_str()
        .split('-')
        .next_back()
        .and_then(|e| e.parse::<u64>().ok())
}

fn decode_merkle_proof(proof_bytes: Vec<u8>) -> Result<MerkleProof, Error> {
    let proof_bytes = CommitmentProofBytes::try_from(proof_bytes).map_err(|e| {
        Error::temp_penumbra_error(format!("couldn't decode CommitmentProofBytes: {}", e))
    })?;
    let raw_proof: RawMerkleProof = RawMerkleProof::try_from(proof_bytes).map_err(|e| {
        Error::temp_penumbra_error(format!("couldn't decode RawMerkleProof: {}", e))
    })?;

    let proof = MerkleProof::from(raw_proof);

    Ok(proof)
}

const LEAF_DOMAIN_SEPARATOR: &[u8] = b"JMT::LeafNode";
const INTERNAL_DOMAIN_SEPARATOR: &[u8] = b"JMT::IntrnalNode";

const SPARSE_MERKLE_PLACEHOLDER_HASH: [u8; 32] = *b"SPARSE_MERKLE_PLACEHOLDER_HASH__";

fn ics23_spec() -> ics23::ProofSpec {
    ics23::ProofSpec {
        leaf_spec: Some(ics23::LeafOp {
            hash: ics23::HashOp::Sha256.into(),
            prehash_key: ics23::HashOp::Sha256.into(),
            prehash_value: ics23::HashOp::Sha256.into(),
            length: ics23::LengthOp::NoPrefix.into(),
            prefix: LEAF_DOMAIN_SEPARATOR.to_vec(),
        }),
        inner_spec: Some(ics23::InnerSpec {
            hash: ics23::HashOp::Sha256.into(),
            child_order: vec![0, 1],
            min_prefix_length: INTERNAL_DOMAIN_SEPARATOR.len() as i32,
            max_prefix_length: INTERNAL_DOMAIN_SEPARATOR.len() as i32,
            child_size: 32,
            empty_child: SPARSE_MERKLE_PLACEHOLDER_HASH.to_vec(),
        }),
        min_depth: 0,
        max_depth: 64,
        prehash_key_before_comparison: true,
    }
}
/// The ICS23 proof spec for penumbra's IBC state; this can be used to verify proofs
/// for other substores in the penumbra state, provided that the data is indeed inside a substore
/// (as opposed to directly in the root store.)
pub static IBC_PROOF_SPECS: Lazy<Vec<ics23::ProofSpec>> =
    Lazy::new(|| vec![ics23_spec(), ics23_spec()]);

async fn fetch_node_info(
    rpc_client: &HttpClient,
    config: &PenumbraConfig,
) -> Result<tendermint::node::Info, Error> {
    crate::time!("fetch_node_info",
    {
        "src_chain": config.id.to_string(),
    });

    rpc_client
        .status()
        .await
        .map(|s| s.node_info)
        .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))
}

fn sort_events_by_sequence(events: &mut [IbcEventWithHeight]) {
    events.sort_by(|a, b| {
        a.event
            .packet()
            .zip(b.event.packet())
            .map(|(pa, pb)| pa.sequence.cmp(&pb.sequence))
            .unwrap_or(Ordering::Equal)
    });
}
