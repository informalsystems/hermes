use alloc::sync::Arc;
use bytes::{Buf, Bytes};
use core::{
    convert::{TryFrom, TryInto},
    future::Future,
    str::FromStr,
    time::Duration,
};
use num_bigint::BigInt;
use std::{cmp::Ordering, thread};

use ibc_proto::protobuf::Protobuf;
use tendermint::block::Height as TmHeight;
use tendermint::node::info::TxIndexStatus;
use tendermint_light_client_verifier::types::LightBlock as TmLightBlock;
use tendermint_rpc::{
    abci::Path as TendermintABCIPath, endpoint::broadcast::tx_sync::Response, endpoint::status,
    Client, HttpClient, Order,
};
use tokio::runtime::Runtime as TokioRuntime;
use tonic::{codegen::http::Uri, metadata::AsciiMetadataValue};
use tracing::{error, instrument, trace, warn};

use ibc_proto::cosmos::staking::v1beta1::Params as StakingParams;
use ibc_relayer_types::clients::ics07_tendermint::client_state::{
    AllowUpdate, ClientState as TmClientState,
};
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TmHeader;
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics02_client::error::Error as ClientError;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::core::ics24_host::path::{
    AcksPath, ChannelEndsPath, ClientConsensusStatePath, ClientStatePath, CommitmentsPath,
    ConnectionsPath, ReceiptsPath, SeqRecvsPath,
};
use ibc_relayer_types::core::ics24_host::{
    ClientUpgradePath, Path, IBC_QUERY_PATH, SDK_UPGRADE_QUERY_PATH,
};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height as ICSHeight;

use crate::chain::client::ClientSettings;
use crate::chain::cosmos::batch::sequential_send_batched_messages_and_wait_commit;
use crate::chain::cosmos::batch::{
    send_batched_messages_and_wait_check_tx, send_batched_messages_and_wait_commit,
};
use crate::chain::cosmos::encode::key_entry_to_signer;
use crate::chain::cosmos::fee::maybe_register_counterparty_payee;
use crate::chain::cosmos::gas::{calculate_fee, mul_ceil};
use crate::chain::cosmos::query::account::get_or_fetch_account;
use crate::chain::cosmos::query::balance::{query_all_balances, query_balance};
use crate::chain::cosmos::query::denom_trace::query_denom_trace;
use crate::chain::cosmos::query::status::query_status;
use crate::chain::cosmos::query::tx::{
    filter_matching_event, query_packets_from_block, query_packets_from_txs, query_txs,
};
use crate::chain::cosmos::query::{abci_query, fetch_version_specs, packet_query, QueryResponse};
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::types::gas::{
    default_gas_from_config, gas_multiplier_from_config, max_gas_from_config,
};
use crate::chain::endpoint::{ChainEndpoint, ChainStatus, HealthCheck};
use crate::chain::requests::{Qualified, QueryPacketEventDataRequest};
use crate::chain::tracking::TrackedMsgs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::ChainConfig;
use crate::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use crate::denom::DenomTrace;
use crate::error::Error;
use crate::event::monitor::{EventReceiver, TxMonitorCmd};
use crate::event::IbcEventWithHeight;
use crate::keyring::{KeyEntry, KeyRing};
use crate::light_client::tendermint::LightClient as TmLightClient;
use crate::light_client::{LightClient, Verified};
use crate::misbehaviour::MisbehaviourEvidence;
use crate::util::pretty::{PrettyConsensusStateWithHeight, PrettyIdentifiedChannel};
use crate::util::pretty::{PrettyIdentifiedClientState, PrettyIdentifiedConnection};
use crate::{account::Balance, event::monitor::EventMonitor};

use super::requests::{
    IncludeProof, QueryChannelClientStateRequest, QueryChannelRequest, QueryChannelsRequest,
    QueryClientConnectionsRequest, QueryClientStateRequest, QueryClientStatesRequest,
    QueryConnectionChannelsRequest, QueryConnectionRequest, QueryConnectionsRequest,
    QueryConsensusStateRequest, QueryConsensusStatesRequest, QueryHeight,
    QueryHostConsensusStateRequest, QueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentRequest, QueryPacketCommitmentsRequest, QueryPacketReceiptRequest,
    QueryTxRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
    QueryUpgradedClientStateRequest, QueryUpgradedConsensusStateRequest,
};

pub mod batch;
pub mod client;
pub mod compatibility;
pub mod encode;
pub mod estimate;
pub mod fee;
pub mod gas;
pub mod query;
pub mod retry;
pub mod simulate;
pub mod tx;
pub mod types;
pub mod version;
pub mod wait;

/// Defines an upper limit on how large any transaction can be.
/// This upper limit is defined as a fraction relative to the block's
/// maximum bytes. For example, if the fraction is `0.9`, then
/// `max_tx_size` will not be allowed to exceed 0.9 of the
/// maximum block size of any Cosmos SDK network.
///
/// The default fraction we use is `0.9`; anything larger than that
/// would be risky, as transactions might be rejected; a smaller value
/// might be un-necessarily restrictive on the relayer side.
/// The [default max. block size in Tendermint 0.37 is 21MB](tm-37-max).
/// With a fraction of `0.9`, then Hermes will never permit the configuration
/// of `max_tx_size` to exceed ~18.9MB.
///
/// [tm-37-max]: https://github.com/tendermint/tendermint/blob/v0.37.0-rc1/types/params.go#L79
pub const BLOCK_MAX_BYTES_MAX_FRACTION: f64 = 0.9;
pub struct CosmosSdkChain {
    config: ChainConfig,
    tx_config: TxConfig,
    rpc_client: HttpClient,
    grpc_addr: Uri,
    light_client: TmLightClient,
    rt: Arc<TokioRuntime>,
    keybase: KeyRing,
    /// A cached copy of the account information
    account: Option<Account>,
}

impl CosmosSdkChain {
    /// Get a reference to the configuration for this chain.
    pub fn config(&self) -> &ChainConfig {
        &self.config
    }

    /// The maximum size of any transaction sent by the relayer to this chain
    fn max_tx_size(&self) -> usize {
        self.config.max_tx_size.into()
    }

    fn key(&self) -> Result<KeyEntry, Error> {
        self.keybase()
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)
    }

    /// Fetches the trusting period as a `Duration` from the chain config.
    /// If no trusting period exists in the config, the trusting period is calculated
    /// as two-thirds of the `unbonding_period`.
    fn trusting_period(&self, unbonding_period: Duration) -> Duration {
        self.config
            .trusting_period
            .unwrap_or(2 * unbonding_period / 3)
    }

    /// Performs validation of the relayer's configuration
    /// for a specific chain against the parameters of that chain.
    ///
    /// Currently, validates the following:
    ///     - the configured `max_tx_size` is appropriate
    ///     - the trusting period is greater than zero
    ///     - the trusting period is smaller than the unbonding period
    ///     - the default gas is smaller than the max gas
    ///
    /// Emits a log warning in case any error is encountered and
    /// exits early without doing subsequent validations.
    pub fn validate_params(&self) -> Result<(), Error> {
        let unbonding_period = self.unbonding_period()?;
        let trusting_period = self.trusting_period(unbonding_period);

        // Check that the trusting period is greater than zero
        if trusting_period <= Duration::ZERO {
            return Err(Error::config_validation_trusting_period_smaller_than_zero(
                self.id().clone(),
                trusting_period,
            ));
        }

        // Check that the trusting period is smaller than the unbounding period
        if trusting_period >= unbonding_period {
            return Err(
                Error::config_validation_trusting_period_greater_than_unbonding_period(
                    self.id().clone(),
                    trusting_period,
                    unbonding_period,
                ),
            );
        }

        let max_gas = max_gas_from_config(&self.config);
        let default_gas = default_gas_from_config(&self.config);

        // If the default gas is strictly greater than the max gas and the tx simulation fails,
        // Hermes won't be able to ever submit that tx because the gas amount wanted will be
        // greater than the max gas.
        if default_gas > max_gas {
            return Err(Error::config_validation_default_gas_too_high(
                self.id().clone(),
                default_gas,
                max_gas,
            ));
        }

        // Get the latest height and convert to tendermint Height
        let latest_height = TmHeight::try_from(self.query_chain_latest_height()?.revision_height())
            .map_err(Error::invalid_height)?;

        // Check on the configured max_tx_size against the consensus parameters at latest height
        let result = self
            .block_on(self.rpc_client.consensus_params(latest_height))
            .map_err(|e| {
                Error::config_validation_json_rpc(
                    self.id().clone(),
                    self.config.rpc_addr.to_string(),
                    "/consensus_params".to_string(),
                    e,
                )
            })?;

        let max_bound = result.consensus_params.block.max_bytes;
        let max_allowed = mul_ceil(max_bound, BLOCK_MAX_BYTES_MAX_FRACTION);
        let max_tx_size = BigInt::from(self.max_tx_size());

        if max_tx_size > max_allowed {
            return Err(Error::config_validation_tx_size_out_of_bounds(
                self.id().clone(),
                self.max_tx_size(),
                max_bound,
            ));
        }

        // Check that the configured max gas is lower or equal to the consensus params max gas.
        let consensus_max_gas = result.consensus_params.block.max_gas;

        // If the consensus max gas is < 0, we don't need to perform the check.
        if consensus_max_gas >= 0 {
            let consensus_max_gas: u64 = consensus_max_gas
                .try_into()
                .expect("cannot over or underflow because it is positive");

            let max_gas = max_gas_from_config(&self.config);

            if max_gas > consensus_max_gas {
                return Err(Error::config_validation_max_gas_too_high(
                    self.id().clone(),
                    max_gas,
                    result.consensus_params.block.max_gas,
                ));
            }
        }

        let gas_multiplier = gas_multiplier_from_config(&self.config);

        if gas_multiplier < 1.1 {
            return Err(Error::config_validation_gas_multiplier_low(
                self.id().clone(),
                gas_multiplier,
            ));
        }

        Ok(())
    }

    /// Query the chain staking parameters
    pub fn query_staking_params(&self) -> Result<StakingParams, Error> {
        crate::time!("query_staking_params");
        crate::telemetry!(query, self.id(), "query_staking_params");

        let mut client = self
            .block_on(
                ibc_proto::cosmos::staking::v1beta1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request =
            tonic::Request::new(ibc_proto::cosmos::staking::v1beta1::QueryParamsRequest {});

        let response = self
            .block_on(client.params(request))
            .map_err(Error::grpc_status)?;

        let params = response
            .into_inner()
            .params
            .ok_or_else(|| Error::grpc_response_param("no staking params".to_string()))?;

        Ok(params)
    }

    /// The unbonding period of this chain
    pub fn unbonding_period(&self) -> Result<Duration, Error> {
        crate::time!("unbonding_period");

        let unbonding_time = self.query_staking_params()?.unbonding_time.ok_or_else(|| {
            Error::grpc_response_param("no unbonding time in staking params".to_string())
        })?;

        Ok(Duration::new(
            unbonding_time.seconds as u64,
            unbonding_time.nanos as u32,
        ))
    }

    /// The number of historical entries kept by this chain
    pub fn historical_entries(&self) -> Result<u32, Error> {
        crate::time!("historical_entries");

        self.query_staking_params().map(|p| p.historical_entries)
    }

    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        crate::time!("block_on");
        self.rt.block_on(f)
    }

    fn query(
        &self,
        data: impl Into<Path>,
        height_query: QueryHeight,
        prove: bool,
    ) -> Result<QueryResponse, Error> {
        crate::time!("query");

        // SAFETY: Creating a Path from a constant; this should never fail
        let path = TendermintABCIPath::from_str(IBC_QUERY_PATH)
            .expect("Turning IBC query path constant into a Tendermint ABCI path");

        let height = TmHeight::try_from(height_query)?;

        let data = data.into();
        if !data.is_provable() & prove {
            return Err(Error::private_store());
        }

        let response = self.block_on(abci_query(
            &self.rpc_client,
            &self.config.rpc_addr,
            path,
            data.to_string(),
            height,
            prove,
        ))?;

        // TODO - Verify response proof, if requested.
        if prove {}

        Ok(response)
    }

    /// Perform an ABCI query against the client upgrade sub-store.
    ///
    /// The data is returned in its raw format `Vec<u8>`, and is either the
    /// client state (if the target path is [`UpgradedClientState`]), or the
    /// client consensus state ([`UpgradedClientConsensusState`]).
    ///
    /// Note: This is a special query in that it will only succeed if the chain
    /// is halted after reaching the height proposed in a successful governance
    /// proposal to upgrade the chain. In this scenario, let P be the height at
    /// which the chain is planned to upgrade. We assume that the chain is
    /// halted at height P. Tendermint will be at height P (as reported by the
    /// /status RPC query), but the application will be at height P-1 (as
    /// reported by the /abci_info RPC query).
    ///
    /// Therefore, `query_height` needs to be P-1. However, the path specified
    /// in `query_data` needs to be constructed with height `P`, as this is how
    /// the chain will have stored it in its upgrade sub-store.
    fn query_client_upgrade_state(
        &self,
        query_data: ClientUpgradePath,
        query_height: ICSHeight,
    ) -> Result<(Vec<u8>, MerkleProof), Error> {
        // SAFETY: Creating a Path from a constant; this should never fail
        let path = TendermintABCIPath::from_str(SDK_UPGRADE_QUERY_PATH)
            .expect("Turning SDK upgrade query path constant into a Tendermint ABCI path");

        let response: QueryResponse = self.block_on(abci_query(
            &self.rpc_client,
            &self.config.rpc_addr,
            path,
            Path::Upgrade(query_data).to_string(),
            TmHeight::try_from(query_height.revision_height()).map_err(Error::invalid_height)?,
            true,
        ))?;

        let proof = response.proof.ok_or_else(Error::empty_response_proof)?;

        Ok((response.value, proof))
    }

    /// Query the chain status via an RPC query.
    ///
    /// Returns an error if the node is still syncing and has not caught up,
    /// ie. if `sync_info.catching_up` is `true`.
    fn chain_status(&self) -> Result<status::Response, Error> {
        crate::time!("chain_status");
        crate::telemetry!(query, self.id(), "status");

        let status = self
            .block_on(self.rpc_client.status())
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        if status.sync_info.catching_up {
            return Err(Error::chain_not_caught_up(
                self.config.rpc_addr.to_string(),
                self.config().id.clone(),
            ));
        }

        Ok(status)
    }

    /// Query the chain's latest height
    pub fn query_chain_latest_height(&self) -> Result<ICSHeight, Error> {
        crate::time!("query_latest_height");
        crate::telemetry!(query, self.id(), "query_latest_height");

        let status = self.rt.block_on(query_status(
            self.id(),
            &self.rpc_client,
            &self.config.rpc_addr,
        ))?;

        Ok(status.height)
    }

    #[instrument(
        name = "send_messages_and_wait_commit",
        level = "error",
        skip_all,
        fields(
            chain = %self.id(),
            tracking_id = %tracked_msgs.tracking_id()
        ),
    )]
    async fn do_send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!("send_messages_and_wait_commit");

        let proto_msgs = tracked_msgs.msgs;

        let key_entry = self.key()?;

        let account =
            get_or_fetch_account(&self.grpc_addr, &key_entry.account, &mut self.account).await?;

        if self.config.sequential_batch_tx {
            sequential_send_batched_messages_and_wait_commit(
                &self.tx_config,
                self.config.max_msg_num,
                self.config.max_tx_size,
                &key_entry,
                account,
                &self.config.memo_prefix,
                proto_msgs,
            )
            .await
        } else {
            send_batched_messages_and_wait_commit(
                &self.tx_config,
                self.config.max_msg_num,
                self.config.max_tx_size,
                &key_entry,
                account,
                &self.config.memo_prefix,
                proto_msgs,
            )
            .await
        }
    }

    #[instrument(
        name = "send_messages_and_wait_check_tx",
        level = "error",
        skip_all,
        fields(
            chain = %self.id(),
            tracking_id = %tracked_msgs.tracking_id()
        ),
    )]
    async fn do_send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<Response>, Error> {
        crate::time!("send_messages_and_wait_check_tx");

        let proto_msgs = tracked_msgs.msgs;

        let key_entry = self.key()?;

        let account =
            get_or_fetch_account(&self.grpc_addr, &key_entry.account, &mut self.account).await?;

        send_batched_messages_and_wait_check_tx(
            &self.tx_config,
            self.config.max_msg_num,
            self.config.max_tx_size,
            &key_entry,
            account,
            &self.config.memo_prefix,
            proto_msgs,
        )
        .await
    }

    fn query_packet_from_block(
        &self,
        request: &QueryPacketEventDataRequest,
        seqs: &[Sequence],
        block_height: &ICSHeight,
    ) -> Result<(Vec<IbcEventWithHeight>, Vec<IbcEventWithHeight>), Error> {
        crate::time!("query_block: query block packet events");
        crate::telemetry!(query, self.id(), "query_block");

        let mut begin_block_events = vec![];
        let mut end_block_events = vec![];

        let tm_height =
            tendermint::block::Height::try_from(block_height.revision_height()).unwrap();

        let response = self
            .block_on(self.rpc_client.block_results(tm_height))
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        let response_height = ICSHeight::new(self.id().version(), u64::from(response.height))
            .map_err(|_| Error::invalid_height_no_source())?;

        begin_block_events.append(
            &mut response
                .begin_block_events
                .unwrap_or_default()
                .into_iter()
                .filter_map(|ev| filter_matching_event(ev, request, seqs))
                .map(|ev| IbcEventWithHeight::new(ev, response_height))
                .collect(),
        );

        end_block_events.append(
            &mut response
                .end_block_events
                .unwrap_or_default()
                .into_iter()
                .filter_map(|ev| filter_matching_event(ev, request, seqs))
                .map(|ev| IbcEventWithHeight::new(ev, response_height))
                .collect(),
        );
        Ok((begin_block_events, end_block_events))
    }

    fn query_packets_from_blocks(
        &self,
        request: &QueryPacketEventDataRequest,
    ) -> Result<(Vec<IbcEventWithHeight>, Vec<IbcEventWithHeight>), Error> {
        crate::time!("query_blocks: query block packet events");
        crate::telemetry!(query, self.id(), "query_blocks");

        let mut begin_block_events = vec![];
        let mut end_block_events = vec![];

        for seq in request.sequences.iter() {
            let response = self
                .block_on(self.rpc_client.block_search(
                    packet_query(request, *seq),
                    1,
                    1, // there should only be a single match for this query
                    Order::Ascending,
                ))
                .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

            assert!(
                response.blocks.len() <= 1,
                "block_search: unexpected number of blocks"
            );

            if let Some(block) = response.blocks.first().map(|first| &first.block) {
                let response_height =
                    ICSHeight::new(self.id().version(), u64::from(block.header.height))
                        .map_err(|_| Error::invalid_height_no_source())?;

                if let QueryHeight::Specific(query_height) = request.height.get() {
                    if response_height > query_height {
                        continue;
                    }
                }

                let (new_begin_block_events, new_end_block_events) =
                    self.query_packet_from_block(request, &[*seq], &response_height)?;

                begin_block_events.extend(new_begin_block_events);
                end_block_events.extend(new_end_block_events);
            }
        }
        Ok((begin_block_events, end_block_events))
    }
}

impl ChainEndpoint for CosmosSdkChain {
    type LightBlock = TmLightBlock;
    type Header = TmHeader;
    type ConsensusState = TMConsensusState;
    type ClientState = TmClientState;

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;

        let light_client = rt.block_on(init_light_client(&rpc_client, &config))?;

        // Initialize key store and load key
        let keybase = KeyRing::new(config.key_store_type, &config.account_prefix, &config.id)
            .map_err(Error::key_base)?;

        let grpc_addr = Uri::from_str(&config.grpc_addr.to_string())
            .map_err(|e| Error::invalid_uri(config.grpc_addr.to_string(), e))?;

        let tx_config = TxConfig::try_from(&config)?;

        // Retrieve the version specification of this chain

        let chain = Self {
            config,
            rpc_client,
            grpc_addr,
            light_client,
            rt,
            keybase,
            account: None,
            tx_config,
        };

        Ok(chain)
    }

    fn init_event_monitor(
        &self,
        rt: Arc<TokioRuntime>,
    ) -> Result<(EventReceiver, TxMonitorCmd), Error> {
        crate::time!("init_event_monitor");

        let (mut event_monitor, event_receiver, monitor_tx) = EventMonitor::new(
            self.config.id.clone(),
            self.config.websocket_addr.clone(),
            rt,
        )
        .map_err(Error::event_monitor)?;

        event_monitor.subscribe().map_err(Error::event_monitor)?;

        thread::spawn(move || event_monitor.run());

        Ok((event_receiver, monitor_tx))
    }

    fn shutdown(self) -> Result<(), Error> {
        Ok(())
    }

    fn keybase(&self) -> &KeyRing {
        &self.keybase
    }

    fn keybase_mut(&mut self) -> &mut KeyRing {
        &mut self.keybase
    }

    /// Does multiple RPC calls to the full node, to check for
    /// reachability and some basic APIs are available.
    ///
    /// Currently this checks that:
    ///     - the node responds OK to `/health` RPC call;
    ///     - the node has transaction indexing enabled;
    ///     - the SDK & IBC versions are supported;
    ///
    /// Emits a log warning in case anything is amiss.
    /// Exits early if any health check fails, without doing any
    /// further checks.
    fn health_check(&self) -> Result<HealthCheck, Error> {
        if let Err(e) = do_health_check(self) {
            warn!("Health checkup for chain '{}' failed", self.id());
            warn!("    Reason: {}", e.detail());
            warn!("    Some Hermes features may not work in this mode!");

            return Ok(HealthCheck::Unhealthy(Box::new(e)));
        }

        if let Err(e) = self.validate_params() {
            warn!("Hermes might be misconfigured for chain '{}'", self.id());
            warn!("    Reason: {}", e.detail());
            warn!("    Some Hermes features may not work in this mode!");

            return Ok(HealthCheck::Unhealthy(Box::new(e)));
        }

        Ok(HealthCheck::Healthy)
    }

    /// Fetch a header from the chain at the given height and verify it.
    fn verify_header(
        &mut self,
        trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        self.light_client
            .verify(trusted, target, client_state)
            .map(|v| v.target)
    }

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.light_client.check_misbehaviour(update, client_state)
    }

    // Queries

    /// Send one or more transactions that include all the specified messages.
    /// The `proto_msgs` are split in transactions such they don't exceed the configured maximum
    /// number of messages per transaction and the maximum transaction size.
    /// Then `send_tx()` is called with each Tx. `send_tx()` determines the fee based on the
    /// on-chain simulation and if this exceeds the maximum gas specified in the configuration file
    /// then it returns error.
    /// TODO - more work is required here for a smarter split maybe iteratively accumulating/ evaluating
    /// msgs in a Tx until any of the max size, max num msgs, max fee are exceeded.
    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let runtime = self.rt.clone();

        runtime.block_on(self.do_send_messages_and_wait_commit(tracked_msgs))
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<Response>, Error> {
        let runtime = self.rt.clone();

        runtime.block_on(self.do_send_messages_and_wait_check_tx(tracked_msgs))
    }

    /// Get the account for the signer
    fn get_signer(&self) -> Result<Signer, Error> {
        crate::time!("get_signer");

        // Get the key from key seed file
        let key_entry = self.key()?;

        let signer = key_entry_to_signer(&key_entry, &self.config.account_prefix)?;

        Ok(signer)
    }

    /// Get the chain configuration
    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        let version_specs = self.block_on(fetch_version_specs(self.id(), &self.grpc_addr))?;
        Ok(version_specs.ibc_go)
    }

    fn query_balance(&self, key_name: Option<&str>, denom: Option<&str>) -> Result<Balance, Error> {
        // If a key_name is given, extract the account hash.
        // Else retrieve the account from the configuration file.
        let account = match key_name {
            Some(key_name) => {
                let key = self.keybase().get_key(key_name).map_err(Error::key_base)?;
                key.account
            }
            _ => self.key()?.account,
        };

        let denom = denom.unwrap_or(&self.config.gas_price.denom);
        let balance = self.block_on(query_balance(&self.grpc_addr, &account, denom))?;

        Ok(balance)
    }

    fn query_all_balances(&self, key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        // If a key_name is given, extract the account hash.
        // Else retrieve the account from the configuration file.
        let account = match key_name {
            Some(key_name) => {
                let key = self.keybase().get_key(key_name).map_err(Error::key_base)?;
                key.account
            }
            _ => self.key()?.account,
        };

        let balance = self.block_on(query_all_balances(&self.grpc_addr, &account))?;

        Ok(balance)
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        let denom_trace = self.block_on(query_denom_trace(&self.grpc_addr, &hash))?;

        Ok(denom_trace)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        crate::time!("query_commitment_prefix");
        crate::telemetry!(query, self.id(), "query_commitment_prefix");

        // TODO - do a real chain query
        CommitmentPrefix::try_from(self.config.store_prefix.as_bytes().to_vec())
            .map_err(|_| Error::ics02(ClientError::empty_prefix()))
    }

    /// Query the application status
    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        crate::time!("query_application_status");
        crate::telemetry!(query, self.id(), "query_application_status");

        // We cannot rely on `/status` endpoint to provide details about the latest block.
        // Instead, we need to pull block height via `/abci_info` and then fetch block
        // metadata at the given height via `/blockchain` endpoint.
        let abci_info = self
            .block_on(self.rpc_client.abci_info())
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        // Query `/blockchain` endpoint to pull the block metadata corresponding to
        // the latest block that the application committed.
        // TODO: Replace this query with `/header`, once it's available.
        //  https://github.com/informalsystems/tendermint-rs/pull/1101
        let blocks = self
            .block_on(
                self.rpc_client
                    .blockchain(abci_info.last_block_height, abci_info.last_block_height),
            )
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?
            .block_metas;

        return if let Some(latest_app_block) = blocks.first() {
            let height = ICSHeight::new(
                ChainId::chain_version(latest_app_block.header.chain_id.as_str()),
                u64::from(abci_info.last_block_height),
            )
            .map_err(|_| Error::invalid_height_no_source())?;
            let timestamp = latest_app_block.header.time.into();

            Ok(ChainStatus { height, timestamp })
        } else {
            // The `/blockchain` query failed to return the header we wanted
            Err(Error::query(
                "/blockchain endpoint for latest app. block".to_owned(),
            ))
        };
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        crate::time!("query_clients");
        crate::telemetry!(query, self.id(), "query_clients");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());
        let response = self
            .block_on(client.client_states(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        // Deserialize into domain type
        let mut clients: Vec<IdentifiedAnyClientState> = response
            .client_states
            .into_iter()
            .filter_map(|cs| {
                IdentifiedAnyClientState::try_from(cs.clone())
                    .map_err(|e| {
                        warn!(
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
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        crate::time!("query_client_state");
        crate::telemetry!(query, self.id(), "query_client_state");

        let res = self.query(
            ClientStatePath(request.client_id.clone()),
            request.height,
            matches!(include_proof, IncludeProof::Yes),
        )?;
        let client_state = AnyClientState::decode_vec(&res.value).map_err(Error::decode)?;

        match include_proof {
            IncludeProof::Yes => {
                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;
                Ok((client_state, Some(proof)))
            }
            IncludeProof::No => Ok((client_state, None)),
        }
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        crate::time!("query_upgraded_client_state");
        crate::telemetry!(query, self.id(), "query_upgraded_client_state");

        // Query for the value and the proof.
        let upgrade_height = request.upgrade_height;
        let query_height = upgrade_height
            .decrement()
            .map_err(|_| Error::invalid_height_no_source())?;

        let (upgraded_client_state_raw, proof) = self.query_client_upgrade_state(
            ClientUpgradePath::UpgradedClientState(upgrade_height.revision_height()),
            query_height,
        )?;

        let client_state = AnyClientState::decode_vec(&upgraded_client_state_raw)
            .map_err(Error::conversion_from_any)?;

        Ok((client_state, proof))
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        crate::time!("query_upgraded_consensus_state");
        crate::telemetry!(query, self.id(), "query_upgraded_consensus_state");

        let upgrade_height = request.upgrade_height;
        let query_height = upgrade_height
            .decrement()
            .map_err(|_| Error::invalid_height_no_source())?;

        // Fetch the consensus state and its proof.
        let (upgraded_consensus_state_raw, proof) = self.query_client_upgrade_state(
            ClientUpgradePath::UpgradedClientConsensusState(upgrade_height.revision_height()),
            query_height,
        )?;

        let consensus_state = AnyConsensusState::decode_vec(&upgraded_consensus_state_raw)
            .map_err(Error::conversion_from_any)?;

        Ok((consensus_state, proof))
    }

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        crate::time!("query_consensus_states");
        crate::telemetry!(query, self.id(), "query_consensus_states");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());
        let response = self
            .block_on(client.consensus_states(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let mut consensus_states: Vec<AnyConsensusStateWithHeight> = response
            .consensus_states
            .into_iter()
            .filter_map(|cs| {
                TryFrom::try_from(cs.clone())
                    .map_err(|e| {
                        warn!(
                            "failed to parse consensus state {}. Error: {}",
                            PrettyConsensusStateWithHeight(&cs),
                            e
                        )
                    })
                    .ok()
            })
            .collect();
        consensus_states.sort_by(|a, b| a.height.cmp(&b.height));
        consensus_states.reverse();
        Ok(consensus_states)
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        crate::time!("query_consensus_state");
        crate::telemetry!(query, self.id(), "query_consensus_state");

        let res = self.query(
            ClientConsensusStatePath {
                client_id: request.client_id.clone(),
                epoch: request.consensus_height.revision_number(),
                height: request.consensus_height.revision_height(),
            },
            request.query_height,
            matches!(include_proof, IncludeProof::Yes),
        )?;

        let consensus_state = AnyConsensusState::decode_vec(&res.value).map_err(Error::decode)?;

        if !matches!(consensus_state, AnyConsensusState::Tendermint(_)) {
            return Err(Error::consensus_state_type_mismatch(
                ClientType::Tendermint,
                consensus_state.client_type(),
            ));
        }

        match include_proof {
            IncludeProof::Yes => {
                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;
                Ok((consensus_state, Some(proof)))
            }
            IncludeProof::No => Ok((consensus_state, None)),
        }
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        crate::time!("query_client_connections");
        crate::telemetry!(query, self.id(), "query_client_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = match self.block_on(client.client_connections(request)) {
            Ok(res) => res.into_inner(),
            Err(e) if e.code() == tonic::Code::NotFound => return Ok(vec![]),
            Err(e) => return Err(Error::grpc_status(e)),
        };

        let ids = response
            .connection_paths
            .iter()
            .filter_map(|id| {
                ConnectionId::from_str(id)
                    .map_err(|e| warn!("connection with ID {} failed parsing. Error: {}", id, e))
                    .ok()
            })
            .collect();

        Ok(ids)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        crate::time!("query_connections");
        crate::telemetry!(query, self.id(), "query_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.connections(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let connections = response
            .connections
            .into_iter()
            .filter_map(|co| {
                IdentifiedConnectionEnd::try_from(co.clone())
                    .map_err(|e| {
                        warn!(
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

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        crate::time!("query_connection");
        crate::telemetry!(query, self.id(), "query_connection");

        async fn do_query_connection(
            chain: &CosmosSdkChain,
            connection_id: &ConnectionId,
            height_query: QueryHeight,
        ) -> Result<ConnectionEnd, Error> {
            use ibc_proto::ibc::core::connection::v1 as connection;
            use tonic::IntoRequest;

            let mut client =
                connection::query_client::QueryClient::connect(chain.grpc_addr.clone())
                    .await
                    .map_err(Error::grpc_transport)?;

            let mut request = connection::QueryConnectionRequest {
                connection_id: connection_id.to_string(),
            }
            .into_request();

            let height_param = AsciiMetadataValue::try_from(height_query)?;

            request
                .metadata_mut()
                .insert("x-cosmos-block-height", height_param);

            let response = client.connection(request).await.map_err(|e| {
                if e.code() == tonic::Code::NotFound {
                    Error::connection_not_found(connection_id.clone())
                } else {
                    Error::grpc_status(e)
                }
            })?;

            match response.into_inner().connection {
                Some(raw_connection) => {
                    let connection_end = raw_connection.try_into().map_err(Error::ics03)?;

                    Ok(connection_end)
                }
                None => {
                    // When no connection is found, the GRPC call itself should return
                    // the NotFound error code. Nevertheless even if the call is successful,
                    // the connection field may not be present, because in protobuf3
                    // everything is optional.
                    Err(Error::connection_not_found(connection_id.clone()))
                }
            }
        }

        match include_proof {
            IncludeProof::Yes => {
                let res = self.query(
                    ConnectionsPath(request.connection_id.clone()),
                    request.height,
                    true,
                )?;
                let connection_end =
                    ConnectionEnd::decode_vec(&res.value).map_err(Error::decode)?;

                Ok((
                    connection_end,
                    Some(res.proof.ok_or_else(Error::empty_response_proof)?),
                ))
            }
            IncludeProof::No => self
                .block_on(async {
                    do_query_connection(self, &request.connection_id, request.height).await
                })
                .map(|conn_end| (conn_end, None)),
        }
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        crate::time!("query_connection_channels");
        crate::telemetry!(query, self.id(), "query_connection_channels");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.connection_channels(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| {
                IdentifiedChannelEnd::try_from(ch.clone())
                    .map_err(|e| {
                        warn!(
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
        crate::time!("query_channels");
        crate::telemetry!(query, self.id(), "query_channels");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.channels(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let channels = response
            .channels
            .into_iter()
            .filter_map(|ch| {
                IdentifiedChannelEnd::try_from(ch.clone())
                    .map_err(|e| {
                        warn!(
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

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        crate::time!("query_channel");
        crate::telemetry!(query, self.id(), "query_channel");

        let res = self.query(
            ChannelEndsPath(request.port_id, request.channel_id),
            request.height,
            matches!(include_proof, IncludeProof::Yes),
        )?;

        let channel_end = ChannelEnd::decode_vec(&res.value).map_err(Error::decode)?;

        match include_proof {
            IncludeProof::Yes => {
                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;
                Ok((channel_end, Some(proof)))
            }
            IncludeProof::No => Ok((channel_end, None)),
        }
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        crate::time!("query_channel_client_state");
        crate::telemetry!(query, self.id(), "query_channel_client_state");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.channel_client_state(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let client_state: Option<IdentifiedAnyClientState> = response
            .identified_client_state
            .map_or_else(|| None, |proto_cs| proto_cs.try_into().ok());

        Ok(client_state)
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let res = self.query(
            CommitmentsPath {
                port_id: request.port_id,
                channel_id: request.channel_id,
                sequence: request.sequence,
            },
            request.height,
            matches!(include_proof, IncludeProof::Yes),
        )?;

        match include_proof {
            IncludeProof::Yes => {
                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;

                Ok((res.value, Some(proof)))
            }
            IncludeProof::No => Ok((res.value, None)),
        }
    }

    /// Queries the packet commitment hashes associated with a channel.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        crate::time!("query_packet_commitments");
        crate::telemetry!(query, self.id(), "query_packet_commitments");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.packet_commitments(request))
            .map_err(Error::grpc_status)?
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
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let res = self.query(
            ReceiptsPath {
                port_id: request.port_id,
                channel_id: request.channel_id,
                sequence: request.sequence,
            },
            request.height,
            matches!(include_proof, IncludeProof::Yes),
        )?;

        match include_proof {
            IncludeProof::Yes => {
                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;

                Ok((res.value, Some(proof)))
            }
            IncludeProof::No => Ok((res.value, None)),
        }
    }

    /// Queries the unreceived packet sequences associated with a channel.
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        crate::time!("query_unreceived_packets");
        crate::telemetry!(query, self.id(), "query_unreceived_packets");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let mut response = self
            .block_on(client.unreceived_packets(request))
            .map_err(Error::grpc_status)?
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
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let res = self.query(
            AcksPath {
                port_id: request.port_id,
                channel_id: request.channel_id,
                sequence: request.sequence,
            },
            request.height,
            matches!(include_proof, IncludeProof::Yes),
        )?;

        match include_proof {
            IncludeProof::Yes => {
                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;

                Ok((res.value, Some(proof)))
            }
            IncludeProof::No => Ok((res.value, None)),
        }
    }

    /// Queries the packet acknowledgment hashes associated with a channel.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        crate::time!("query_packet_acknowledgements");
        crate::telemetry!(query, self.id(), "query_packet_acknowledgements");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let response = self
            .block_on(client.packet_acknowledgements(request))
            .map_err(Error::grpc_status)?
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

    /// Queries the unreceived acknowledgements sequences associated with a channel.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        crate::time!("query_unreceived_acknowledgements");
        crate::telemetry!(query, self.id(), "query_unreceived_acknowledgements");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request.into());

        let mut response = self
            .block_on(client.unreceived_acks(request))
            .map_err(Error::grpc_status)?
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
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        crate::time!("query_next_sequence_receive");
        crate::telemetry!(query, self.id(), "query_next_sequence_receive");

        match include_proof {
            IncludeProof::Yes => {
                let res = self.query(
                    SeqRecvsPath(request.port_id, request.channel_id),
                    request.height,
                    true,
                )?;

                // Note: We expect the return to be a u64 encoded in big-endian. Refer to ibc-go:
                // https://github.com/cosmos/ibc-go/blob/25767f6bdb5bab2c2a116b41d92d753c93e18121/modules/core/04-channel/client/utils/utils.go#L191
                if res.value.len() != 8 {
                    return Err(Error::query("next_sequence_receive".into()));
                }
                let seq: Sequence = Bytes::from(res.value).get_u64().into();

                let proof = res.proof.ok_or_else(Error::empty_response_proof)?;

                Ok((seq, Some(proof)))
            }
            IncludeProof::No => {
                let mut client = self
                    .block_on(
                        ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                            self.grpc_addr.clone(),
                        ),
                    )
                    .map_err(Error::grpc_transport)?;

                let request = tonic::Request::new(request.into());

                let response = self
                    .block_on(client.next_sequence_receive(request))
                    .map_err(Error::grpc_status)?
                    .into_inner();

                Ok((Sequence::from(response.next_sequence_receive), None))
            }
        }
    }

    /// This function queries transactions for events matching certain criteria.
    /// 1. Client Update request - returns a vector with at most one update client event
    /// 2. Transaction event request - returns all IBC events resulted from a Tx execution
    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!("query_txs");
        crate::telemetry!(query, self.id(), "query_txs");

        self.block_on(query_txs(
            self.id(),
            &self.rpc_client,
            &self.config.rpc_addr,
            request,
        ))
    }

    /// This function queries transactions for packet events matching certain criteria.
    /// It returns at most one packet event for each sequence specified in the request.
    ///    Note - there is no way to format the packet query such that it asks for Tx-es with either
    ///    sequence (the query conditions can only be AND-ed).
    ///    There is a possibility to include "<=" and ">=" conditions but it doesn't work with
    ///    string attributes (sequence is emmitted as a string).
    ///    Therefore, for packets we perform one tx_search for each sequence.
    ///    Alternatively, a single query for all packets could be performed but it would return all
    ///    packets ever sent.
    fn query_packet_events(
        &self,
        mut request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!("query_packet_events");
        crate::telemetry!(query, self.id(), "query_packet_events");

        match request.height {
            // Usage note: `Qualified::Equal` is currently only used in the call hierarchy involving
            // the CLI methods, namely the CLI for `tx packet-recv` and `tx packet-ack` when the
            // user passes the flag `packet-data-query-height`.
            Qualified::Equal(_) => self.block_on(query_packets_from_block(
                self.id(),
                &self.rpc_client,
                &self.config.rpc_addr,
                &request,
            )),
            Qualified::SmallerEqual(_) => {
                let tx_events = self.block_on(query_packets_from_txs(
                    self.id(),
                    &self.rpc_client,
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
                    self.query_packets_from_blocks(&request)?
                } else {
                    Default::default()
                };

                trace!("start_block_events {:?}", start_block_events);
                trace!("tx_events {:?}", tx_events);
                trace!("end_block_events {:?}", end_block_events);

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
        request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        let height = match request.height {
            QueryHeight::Latest => TmHeight::from(0u32),
            QueryHeight::Specific(ibc_height) => {
                TmHeight::try_from(ibc_height.revision_height()).map_err(Error::invalid_height)?
            }
        };

        // TODO(hu55a1n1): use the `/header` RPC endpoint instead when we move to tendermint v0.35.x
        let rpc_call = match height.value() {
            0 => self.rpc_client.latest_block(),
            _ => self.rpc_client.block(height),
        };
        let response = self
            .block_on(rpc_call)
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;
        Ok(response.block.header.into())
    }

    fn build_client_state(
        &self,
        height: ICSHeight,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        let ClientSettings::Tendermint(settings) = settings;
        let unbonding_period = self.unbonding_period()?;
        let trusting_period = settings
            .trusting_period
            .unwrap_or_else(|| self.trusting_period(unbonding_period));

        let proof_specs = self.config.proof_specs.clone().unwrap_or_default();

        // Build the client state.
        TmClientState::new(
            self.id().clone(),
            settings.trust_threshold,
            trusting_period,
            unbonding_period,
            settings.max_clock_drift,
            height,
            proof_specs,
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
        crate::time!("build_consensus_state");

        Ok(TMConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &mut self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        crate::time!("build_header");

        // Get the light block at target_height from chain.
        let Verified { target, supporting } = self.light_client.header_and_minimal_set(
            trusted_height,
            target_height,
            client_state,
        )?;

        Ok((target, supporting))
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_payee: &Signer,
    ) -> Result<(), Error> {
        let address = self.get_signer()?;
        let key_entry = self.key()?;

        self.rt.block_on(maybe_register_counterparty_payee(
            &self.tx_config,
            &key_entry,
            &mut self.account,
            &self.config.memo_prefix,
            channel_id,
            port_id,
            &address,
            counterparty_payee,
        ))
    }
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

/// Initialize the light client for the given chain using the given HTTP client
/// to fetch the node identifier to be used as peer id in the light client.
async fn init_light_client(
    rpc_client: &HttpClient,
    config: &ChainConfig,
) -> Result<TmLightClient, Error> {
    use tendermint_light_client_verifier::types::PeerId;

    crate::time!("init_light_client");

    let peer_id: PeerId = rpc_client
        .status()
        .await
        .map(|s| s.node_info.id)
        .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;

    let light_client = TmLightClient::from_config(config, peer_id)?;

    Ok(light_client)
}

/// Returns the suffix counter for a CosmosSDK client id.
/// Returns `None` if the client identifier is malformed
/// and the suffix could not be parsed.
fn client_id_suffix(client_id: &ClientId) -> Option<u64> {
    client_id
        .as_str()
        .split('-')
        .last()
        .and_then(|e| e.parse::<u64>().ok())
}

fn do_health_check(chain: &CosmosSdkChain) -> Result<(), Error> {
    let chain_id = chain.id();
    let grpc_address = chain.grpc_addr.to_string();
    let rpc_address = chain.config.rpc_addr.to_string();

    // Checkup on the self-reported health endpoint
    chain.block_on(chain.rpc_client.health()).map_err(|e| {
        Error::health_check_json_rpc(
            chain_id.clone(),
            rpc_address.clone(),
            "/health".to_string(),
            e,
        )
    })?;

    // Check that the staking module maintains some historical entries, meaning that
    // local header information is stored in the IBC state and therefore client
    // proofs that are part of the connection handshake messages can be verified.
    if chain.historical_entries()? == 0 {
        return Err(Error::no_historical_entries(chain_id.clone()));
    }

    let status = chain.chain_status()?;

    // Check that transaction indexing is enabled
    if status.node_info.other.tx_index != TxIndexStatus::On {
        return Err(Error::tx_indexing_disabled(chain_id.clone()));
    }

    // Check that the chain identifier matches the network name
    if status.node_info.network.as_str() != chain_id.as_str() {
        // Log the error, continue optimistically
        error!(
            "/status endpoint from chain '{}' reports network identifier to be '{}'. \
            This is usually a sign of misconfiguration, please check your config.toml",
            chain_id, status.node_info.network
        );
    }

    let version_specs = chain.block_on(fetch_version_specs(&chain.config.id, &chain.grpc_addr))?;

    // Checkup on the underlying SDK & IBC-go versions
    if let Err(diagnostic) = compatibility::run_diagnostic(&version_specs) {
        return Err(Error::sdk_module_version(
            chain_id.clone(),
            grpc_address,
            diagnostic.to_string(),
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use ibc_relayer_types::{
        core::{ics02_client::client_type::ClientType, ics24_host::identifier::ClientId},
        mock::client_state::MockClientState,
        mock::header::MockHeader,
        Height,
    };

    use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
    use crate::{chain::cosmos::client_id_suffix, config::GasPrice};

    use super::calculate_fee;

    #[test]
    fn mul_ceil() {
        // Because 0.001 cannot be expressed precisely
        // as a 64-bit floating point number (it is
        // stored as 0.001000000047497451305389404296875),
        // `num_rational::BigRational` will represent it as
        // 1152921504606847/1152921504606846976 instead
        // which will sometimes round up to the next
        // integer in the computations below.
        // This is not a problem for the way we compute the fee
        // and gas adjustment as those are already based on simulated
        // gas which is not 100% precise.
        assert_eq!(super::mul_ceil(300_000, 0.001), 301.into());
        assert_eq!(super::mul_ceil(300_004, 0.001), 301.into());
        assert_eq!(super::mul_ceil(300_040, 0.001), 301.into());
        assert_eq!(super::mul_ceil(300_400, 0.001), 301.into());
        assert_eq!(super::mul_ceil(304_000, 0.001), 305.into());
        assert_eq!(super::mul_ceil(340_000, 0.001), 341.into());
        assert_eq!(super::mul_ceil(340_001, 0.001), 341.into());
    }

    /// Before https://github.com/informalsystems/hermes/pull/1568,
    /// this test would have panic'ed with:
    ///
    /// thread 'chain::cosmos::tests::fee_overflow' panicked at 'attempt to multiply with overflow'
    #[test]
    fn fee_overflow() {
        let gas_amount = 90000000000000_u64;
        let gas_price = GasPrice {
            price: 1000000000000.0,
            denom: "uatom".to_string(),
        };

        let fee = calculate_fee(gas_amount, &gas_price);
        assert_eq!(&fee.amount, "90000000000000000000000000");
    }

    #[test]
    fn sort_clients_id_suffix() {
        let mut clients: Vec<IdentifiedAnyClientState> = vec![
            IdentifiedAnyClientState::new(
                ClientId::new(ClientType::Tendermint, 4).unwrap(),
                AnyClientState::Mock(MockClientState::new(MockHeader::new(
                    Height::new(0, 1).unwrap(),
                ))),
            ),
            IdentifiedAnyClientState::new(
                ClientId::new(ClientType::Tendermint, 1).unwrap(),
                AnyClientState::Mock(MockClientState::new(MockHeader::new(
                    Height::new(0, 1).unwrap(),
                ))),
            ),
            IdentifiedAnyClientState::new(
                ClientId::new(ClientType::Tendermint, 7).unwrap(),
                AnyClientState::Mock(MockClientState::new(MockHeader::new(
                    Height::new(0, 1).unwrap(),
                ))),
            ),
        ];
        clients.sort_by_cached_key(|c| client_id_suffix(&c.client_id).unwrap_or(0));
        assert_eq!(
            client_id_suffix(&clients.first().unwrap().client_id).unwrap(),
            1
        );
        assert_eq!(client_id_suffix(&clients[1].client_id).unwrap(), 4);
        assert_eq!(
            client_id_suffix(&clients.last().unwrap().client_id).unwrap(),
            7
        );
    }
}
