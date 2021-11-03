use alloc::sync::Arc;
use core::{
    cmp::min,
    convert::{TryFrom, TryInto},
    future::Future,
    str::FromStr,
    time::Duration,
};
use std::{fmt, thread, time::Instant};

use bech32::{ToBase32, Variant};
use bitcoin::hashes::hex::ToHex;
use chrono::DateTime;
use itertools::Itertools;
use prost::Message;
use prost_types::Any;
use tendermint::abci::{Event, Path as TendermintABCIPath};
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::consensus::Params;
use tendermint_light_client::types::LightBlock as TMLightBlock;
use tendermint_proto::Protobuf;
use tendermint_rpc::endpoint::tx::Response as ResultTx;
use tendermint_rpc::query::{EventType, Query};
use tendermint_rpc::{
    endpoint::broadcast::tx_sync::Response, endpoint::status, Client, HttpClient, Order,
};
use tokio::runtime::Runtime as TokioRuntime;
use tonic::codegen::http::Uri;
use tracing::{debug, error, trace, warn};

use ibc::clients::ics07_tendermint::client_state::{AllowUpdate, ClientState};
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use ibc::clients::ics07_tendermint::header::Header as TmHeader;
use ibc::core::ics02_client::client_consensus::{
    AnyConsensusState, AnyConsensusStateWithHeight, QueryClientEventRequest,
};
use ibc::core::ics02_client::client_state::{AnyClientState, IdentifiedAnyClientState};
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics02_client::events as ClientEvents;
use ibc::core::ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd};
use ibc::core::ics04_channel::channel::{
    ChannelEnd, IdentifiedChannelEnd, QueryPacketEventDataRequest,
};
use ibc::core::ics04_channel::events as ChannelEvents;
use ibc::core::ics04_channel::packet::{Packet, PacketMsgType, Sequence};
use ibc::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc::core::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::core::ics24_host::Path::ClientConsensusState as ClientConsensusPath;
use ibc::core::ics24_host::Path::ClientState as ClientStatePath;
use ibc::core::ics24_host::{ClientUpgradePath, Path, IBC_QUERY_PATH, SDK_UPGRADE_QUERY_PATH};
use ibc::events::{from_tx_response_event, IbcEvent};
use ibc::query::{QueryTxHash, QueryTxRequest};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height as ICSHeight;
use ibc::{downcast, query::QueryBlockRequest};
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, EthAccount, QueryAccountRequest};
use ibc_proto::cosmos::base::tendermint::v1beta1::service_client::ServiceClient;
use ibc_proto::cosmos::base::tendermint::v1beta1::GetNodeInfoRequest;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{
    AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, SimulateRequest, SimulateResponse, Tx, TxBody,
    TxRaw,
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

use crate::event::monitor::{EventMonitor, EventReceiver};
use crate::keyring::{KeyEntry, KeyRing, Store};
use crate::light_client::tendermint::LightClient as TmLightClient;
use crate::light_client::LightClient;
use crate::light_client::Verified;
use crate::{chain::QueryResponse, chain::StatusResponse, event::monitor::TxMonitorCmd};
use crate::{config::types::Memo, error::Error};
use crate::{
    config::{AddressType, ChainConfig, GasPrice},
    sdk_error::sdk_error_from_tx_sync_error_code,
};

use super::{ChainEndpoint, HealthCheck};

mod compatibility;
pub mod version;

/// Default gas limit when submitting a transaction.
const DEFAULT_MAX_GAS: u64 = 300_000;

/// Fraction of the estimated gas to add to the estimated gas amount when submitting a transaction.
const DEFAULT_GAS_PRICE_ADJUSTMENT: f64 = 0.1;

/// Upper limit on the size of transactions submitted by Hermes, expressed as a
/// fraction of the maximum block size defined in the Tendermint core consensus parameters.
pub const GENESIS_MAX_BYTES_MAX_FRACTION: f64 = 0.9;

mod retry_strategy {
    use crate::util::retry::Fixed;
    use core::time::Duration;

    pub fn wait_for_block_commits(max_total_wait: Duration) -> impl Iterator<Item = Duration> {
        let backoff_millis = 300; // The periodic backoff
        let count: usize = (max_total_wait.as_millis() / backoff_millis as u128) as usize;
        Fixed::from_millis(backoff_millis).take(count)
    }
}

pub struct CosmosSdkChain {
    config: ChainConfig,
    version_specs: version::Specs,
    rpc_client: HttpClient,
    grpc_addr: Uri,
    rt: Arc<TokioRuntime>,
    keybase: KeyRing,
    /// A cached copy of the account information
    account: Option<BaseAccount>,
}

impl CosmosSdkChain {
    /// Performs validation of chain-specific configuration
    /// parameters against the chain's genesis configuration.
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

        // If the default gas is strictly greater than the max gas and the tx simulation fails,
        // Hermes won't be able to ever submit that tx because the gas amount wanted will be
        // greater than the max gas.
        if self.default_gas() > self.max_gas() {
            return Err(Error::config_validation_default_gas_too_high(
                self.id().clone(),
                self.default_gas(),
                self.max_gas(),
            ));
        }

        // Get the latest height and convert to tendermint Height
        let latest_height = Height::try_from(self.query_latest_height()?.revision_height)
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
        let max_allowed = mul_ceil(max_bound, GENESIS_MAX_BYTES_MAX_FRACTION) as usize;

        if self.max_tx_size() > max_allowed {
            return Err(Error::config_validation_tx_size_out_of_bounds(
                self.id().clone(),
                self.max_tx_size(),
                max_bound,
            ));
        }

        Ok(())
    }

    /// The unbonding period of this chain
    pub fn unbonding_period(&self) -> Result<Duration, Error> {
        crate::time!("unbonding_period");

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

        let res = response
            .into_inner()
            .params
            .ok_or_else(|| Error::grpc_response_param("none staking params".to_string()))?
            .unbonding_time
            .ok_or_else(|| Error::grpc_response_param("none unbonding time".to_string()))?;

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
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?
            .consensus_params)
    }

    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        crate::time!("block_on");
        self.rt.block_on(f)
    }

    fn send_tx(&mut self, proto_msgs: Vec<Any>) -> Result<Response, Error> {
        crate::time!("send_tx");

        let account_seq = self.account_sequence()?;

        debug!(
            "[{}] send_tx: sending {} messages using account sequence {}",
            self.id(),
            proto_msgs.len(),
            account_seq,
        );

        let signer_info = self.signer(account_seq)?;
        let max_fee = self.max_fee();

        debug!(
            "[{}] send_tx: max fee, for use in tx simulation: {}",
            self.id(),
            PrettyFee(&max_fee)
        );

        let (body, body_buf) = tx_body_and_bytes(proto_msgs, self.tx_memo())?;

        let (auth_info, auth_buf) = auth_info_and_bytes(signer_info.clone(), max_fee)?;
        let signed_doc = self.signed_doc(body_buf.clone(), auth_buf, account_seq)?;

        let simulate_tx = Tx {
            body: Some(body),
            auth_info: Some(auth_info),
            signatures: vec![signed_doc],
        };

        let estimated_gas = self.estimate_gas(simulate_tx)?;
        let adjusted_fee = self.fee_with_gas(estimated_gas);

        debug!(
            "[{}] send_tx: using {} gas, fee {}",
            self.id(),
            estimated_gas,
            PrettyFee(&adjusted_fee)
        );

        let (_auth_adjusted, auth_buf_adjusted) = auth_info_and_bytes(signer_info, adjusted_fee)?;
        let account_number = self.account_number()?;
        let signed_doc =
            self.signed_doc(body_buf.clone(), auth_buf_adjusted.clone(), account_number)?;

        let tx_raw = TxRaw {
            body_bytes: body_buf,
            auth_info_bytes: auth_buf_adjusted,
            signatures: vec![signed_doc],
        };

        let mut tx_bytes = Vec::new();
        prost::Message::encode(&tx_raw, &mut tx_bytes).unwrap();

        let response = self.block_on(broadcast_tx_sync(self, tx_bytes))?;

        match response.code {
            tendermint::abci::Code::Ok => {
                // A success means the account s.n. was increased
                self.incr_account_sequence()?;
                debug!("[{}] send_tx: broadcast_tx_sync: {:?}", self.id(), response);
            }
            tendermint::abci::Code::Err(code) => {
                // Avoid increasing the account s.n. if CheckTx failed
                // Log the error
                error!(
                    "[{}] send_tx: broadcast_tx_sync: {:?}: diagnostic: {:?}",
                    self.id(),
                    response,
                    sdk_error_from_tx_sync_error_code(code)
                );
            }
        }

        Ok(response)
    }

    /// Try to simulate the given tx in order to estimate how much gas will be needed to submit it.
    ///
    /// It is possible that a batch of messages are fragmented by the caller (`send_msgs`) such that
    /// they do not individually verify. For example for the following batch
    /// [`MsgUpdateClient`, `MsgRecvPacket`, ..., `MsgRecvPacket`]
    /// if the batch is split in two TX-es, the second one will fail the simulation in `deliverTx` check
    /// In this case we use the `default_gas` param.
    fn estimate_gas(&self, tx: Tx) -> Result<u64, Error> {
        let estimated_gas = self.send_tx_simulate(tx).map(|sr| sr.gas_info);

        if let Ok(ref gas) = estimated_gas {
            debug!(
                "[{}] send_tx: tx simulation successful, simulated gas: {:?}",
                self.id(),
                gas
            );
        }

        let estimated_gas = estimated_gas.map_or_else(
            |e| {
                error!(
                    "[{}] send_tx: failed to estimate gas, falling back on default gas, error: {}",
                    self.id(),
                    e.detail()
                );

                self.default_gas()
            },
            |gas_info| gas_info.map_or(self.default_gas(), |g| g.gas_used),
        );

        if estimated_gas > self.max_gas() {
            debug!(estimated = ?estimated_gas, max = ?self.max_gas(), "[{}] send_tx: estimated gas is higher than max gas", self.id());

            return Err(Error::tx_simulate_gas_estimate_exceeded(
                self.id().clone(),
                estimated_gas,
                self.max_gas(),
            ));
        }

        Ok(estimated_gas)
    }

    /// The default amount of gas the relayer is willing to pay for a transaction,
    /// when it cannot simulate the tx and therefore estimate the gas amount needed.
    fn default_gas(&self) -> u64 {
        self.config.default_gas.unwrap_or_else(|| self.max_gas())
    }

    /// The maximum amount of gas the relayer is willing to pay for a transaction
    fn max_gas(&self) -> u64 {
        self.config.max_gas.unwrap_or(DEFAULT_MAX_GAS)
    }

    /// The gas price
    fn gas_price(&self) -> &GasPrice {
        &self.config.gas_price
    }

    /// The gas price adjustment
    fn gas_adjustment(&self) -> f64 {
        self.config
            .gas_adjustment
            .unwrap_or(DEFAULT_GAS_PRICE_ADJUSTMENT)
    }

    /// Adjusts the fee based on the configured `gas_adjustment` to prevent out of gas errors.
    /// The actual gas cost, when a transaction is executed, may be slightly higher than the
    /// one returned by the simulation.
    fn apply_adjustment_to_gas(&self, gas_amount: u64) -> u64 {
        min(
            gas_amount + mul_ceil(gas_amount, self.gas_adjustment()),
            self.max_gas(),
        )
    }

    /// The maximum fee the relayer pays for a transaction
    fn max_fee_in_coins(&self) -> Coin {
        calculate_fee(self.max_gas(), self.gas_price())
    }

    /// The fee in coins based on gas amount
    fn fee_from_gas_in_coins(&self, gas: u64) -> Coin {
        calculate_fee(gas, self.gas_price())
    }

    /// The maximum number of messages included in a transaction
    fn max_msg_num(&self) -> usize {
        self.config.max_msg_num.into()
    }

    /// The maximum size of any transaction sent by the relayer to this chain
    fn max_tx_size(&self) -> usize {
        self.config.max_tx_size.into()
    }

    fn query(&self, data: Path, height: ICSHeight, prove: bool) -> Result<QueryResponse, Error> {
        crate::time!("query");

        let path = TendermintABCIPath::from_str(IBC_QUERY_PATH).unwrap();

        let height = Height::try_from(height.revision_height).map_err(Error::invalid_height)?;

        if !data.is_provable() & prove {
            return Err(Error::private_store());
        }

        let response = self.block_on(abci_query(self, path, data.to_string(), height, prove))?;

        // TODO - Verify response proof, if requested.
        if prove {}

        Ok(response)
    }

    /// Perform an ABCI query against the client upgrade sub-store.
    /// Fetches both the target data, as well as the proof.
    ///
    /// The data is returned in its raw format `Vec<u8>`, and is either
    /// the client state (if the target path is [`UpgradedClientState`]),
    /// or the client consensus state ([`UpgradedClientConsensusState`]).
    fn query_client_upgrade_state(
        &self,
        data: ClientUpgradePath,
        height: Height,
    ) -> Result<(Vec<u8>, MerkleProof), Error> {
        let prev_height = Height::try_from(height.value() - 1).map_err(Error::invalid_height)?;

        let path = TendermintABCIPath::from_str(SDK_UPGRADE_QUERY_PATH).unwrap();
        let response: QueryResponse = self.block_on(abci_query(
            self,
            path,
            Path::Upgrade(data).to_string(),
            prev_height,
            true,
        ))?;

        let proof = response.proof.ok_or_else(Error::empty_response_proof)?;

        Ok((response.value, proof))
    }

    fn send_tx_simulate(&self, tx: Tx) -> Result<SimulateResponse, Error> {
        crate::time!("send_tx_simulate");

        use ibc_proto::cosmos::tx::v1beta1::service_client::ServiceClient;

        // The `tx` field of `SimulateRequest` was deprecated in Cosmos SDK 0.43 in favor of `tx_bytes`.
        let mut tx_bytes = vec![];
        prost::Message::encode(&tx, &mut tx_bytes).unwrap(); // FIXME: Handle error here

        #[allow(deprecated)]
        let req = SimulateRequest {
            tx: Some(tx), // needed for simulation to go through with Cosmos SDK <  0.43
            tx_bytes,     // needed for simulation to go through with Cosmos SDk >= 0.43
        };

        let mut client = self
            .block_on(ServiceClient::connect(self.grpc_addr.clone()))
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(req);
        let response = self
            .block_on(client.simulate(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        Ok(response)
    }

    fn key(&self) -> Result<KeyEntry, Error> {
        self.keybase()
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)
    }

    fn key_bytes(&self, key: &KeyEntry) -> Result<Vec<u8>, Error> {
        let mut pk_buf = Vec::new();
        prost::Message::encode(&key.public_key.public_key.to_bytes(), &mut pk_buf).unwrap();
        Ok(pk_buf)
    }

    fn key_and_bytes(&self) -> Result<(KeyEntry, Vec<u8>), Error> {
        let key = self.key()?;
        let key_bytes = self.key_bytes(&key)?;
        Ok((key, key_bytes))
    }

    fn account(&mut self) -> Result<&mut BaseAccount, Error> {
        if self.account == None {
            let account = self.block_on(query_account(self, self.key()?.account))?;
            debug!(
                sequence = %account.sequence,
                number = %account.account_number,
                "[{}] send_tx: retrieved account",
                self.id()
            );
            self.account = Some(account);
        }

        Ok(self
            .account
            .as_mut()
            .expect("account was supposedly just cached"))
    }

    fn account_number(&mut self) -> Result<u64, Error> {
        Ok(self.account()?.account_number)
    }

    fn account_sequence(&mut self) -> Result<u64, Error> {
        Ok(self.account()?.sequence)
    }

    fn incr_account_sequence(&mut self) -> Result<(), Error> {
        self.account()?.sequence += 1;
        Ok(())
    }

    fn signer(&self, sequence: u64) -> Result<SignerInfo, Error> {
        let (_key, pk_buf) = self.key_and_bytes()?;
        let pk_type = match &self.config.address_type {
            AddressType::Cosmos => "/cosmos.crypto.secp256k1.PubKey".to_string(),
            AddressType::Ethermint { pk_type } => pk_type.clone(),
        };
        // Create a MsgSend proto Any message
        let pk_any = Any {
            type_url: pk_type,
            value: pk_buf,
        };

        let single = Single { mode: 1 };
        let sum_single = Some(Sum::Single(single));
        let mode = Some(ModeInfo { sum: sum_single });
        let signer_info = SignerInfo {
            public_key: Some(pk_any),
            mode_info: mode,
            sequence,
        };
        Ok(signer_info)
    }

    fn max_fee(&self) -> Fee {
        Fee {
            amount: vec![self.max_fee_in_coins()],
            gas_limit: self.max_gas(),
            payer: "".to_string(),
            granter: "".to_string(),
        }
    }

    fn fee_with_gas(&self, gas_limit: u64) -> Fee {
        let adjusted_gas_limit = self.apply_adjustment_to_gas(gas_limit);

        Fee {
            amount: vec![self.fee_from_gas_in_coins(adjusted_gas_limit)],
            gas_limit: adjusted_gas_limit,
            payer: "".to_string(),
            granter: "".to_string(),
        }
    }

    fn signed_doc(
        &self,
        body_bytes: Vec<u8>,
        auth_info_bytes: Vec<u8>,
        account_number: u64,
    ) -> Result<Vec<u8>, Error> {
        let sign_doc = SignDoc {
            body_bytes,
            auth_info_bytes,
            chain_id: self.config.clone().id.to_string(),
            account_number,
        };

        // A protobuf serialization of a SignDoc
        let mut signdoc_buf = Vec::new();
        prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

        // Sign doc
        let signed = self
            .keybase
            .sign_msg(
                &self.config.key_name,
                signdoc_buf,
                &self.config.address_type,
            )
            .map_err(Error::key_base)?;

        Ok(signed)
    }

    /// Given a vector of `TxSyncResult` elements,
    /// each including a transaction response hash for one or more messages, periodically queries the chain
    /// with the transaction hashes to get the list of IbcEvents included in those transactions.
    pub fn wait_for_block_commits(
        &self,
        mut tx_sync_results: Vec<TxSyncResult>,
    ) -> Result<Vec<TxSyncResult>, Error> {
        use crate::util::retry::{retry_with_index, RetryResult};

        let hashes = tx_sync_results
            .iter()
            .map(|res| res.response.hash.to_string())
            .join(", ");

        warn!(
            "[{}] waiting for commit of tx hashes(s) {}",
            self.id(),
            hashes
        );

        // Wait a little bit initially
        thread::sleep(Duration::from_millis(200));

        let start = Instant::now();
        let result = retry_with_index(
            retry_strategy::wait_for_block_commits(self.config.rpc_timeout),
            |index| {
                if all_tx_results_found(&tx_sync_results) {
                    trace!(
                        "[{}] wait_for_block_commits: retrieved {} tx results after {} tries ({}ms)",
                        self.id(),
                        tx_sync_results.len(),
                        index,
                        start.elapsed().as_millis()
                    );

                    // All transactions confirmed
                    return RetryResult::Ok(());
                }

                for TxSyncResult { response, events } in tx_sync_results.iter_mut() {
                    // If this transaction was not committed, determine whether it was because it failed
                    // or because it hasn't been committed yet.
                    if empty_event_present(events) {
                        // If the transaction failed, replace the events with an error,
                        // so that we don't attempt to resolve the transaction later on.
                        if response.code.value() != 0 {
                            *events = vec![IbcEvent::ChainError(format!(
                                "deliver_tx on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
                                self.id(), response.hash, response.code, response.log
                            ))];

                            // Otherwise, try to resolve transaction hash to the corresponding events.
                        } else if let Ok(events_per_tx) =
                            self.query_txs(QueryTxRequest::Transaction(QueryTxHash(response.hash)))
                        {
                            // If we get events back, progress was made, so we replace the events
                            // with the new ones. in both cases we will check in the next iteration
                            // whether or not the transaction was fully committed.
                            if !events_per_tx.is_empty() {
                                *events = events_per_tx;
                            }
                        }
                    }
                }
                RetryResult::Retry(index)
            },
        );

        match result {
            // All transactions confirmed
            Ok(()) => Ok(tx_sync_results),
            // Did not find confirmation
            Err(_) => Err(Error::tx_no_confirmation()),
        }
    }

    fn trusting_period(&self, unbonding_period: Duration) -> Duration {
        self.config
            .trusting_period
            .unwrap_or(2 * unbonding_period / 3)
    }

    /// Returns the preconfigured memo to be used for every submitted transaction
    fn tx_memo(&self) -> &Memo {
        &self.config.memo_prefix
    }

    /// Query the chain status via an RPC query
    fn status(&self) -> Result<status::Response, Error> {
        let status = self
            .block_on(self.rpc_client().status())
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
    pub fn query_latest_height(&self) -> Result<ICSHeight, Error> {
        let status = self.status()?;
        Ok(ICSHeight {
            revision_number: ChainId::chain_version(status.node_info.network.as_str()),
            revision_height: u64::from(status.sync_info.latest_block_height),
        })
    }
}

fn empty_event_present(events: &[IbcEvent]) -> bool {
    events.iter().any(|ev| matches!(ev, IbcEvent::Empty(_)))
}

fn all_tx_results_found(tx_sync_results: &[TxSyncResult]) -> bool {
    tx_sync_results
        .iter()
        .all(|r| !empty_event_present(&r.events))
}

impl ChainEndpoint for CosmosSdkChain {
    type LightBlock = TMLightBlock;
    type Header = TmHeader;
    type ConsensusState = TMConsensusState;
    type ClientState = ClientState;
    type LightClient = TmLightClient;

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        let rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;

        // Initialize key store and load key
        let keybase = KeyRing::new(Store::Test, &config.account_prefix, &config.id)
            .map_err(Error::key_base)?;

        let grpc_addr = Uri::from_str(&config.grpc_addr.to_string())
            .map_err(|e| Error::invalid_uri(config.grpc_addr.to_string(), e))?;

        // Retrieve the version specification of this chain
        let version_specs = rt.block_on(fetch_version_specs(&config.id, &grpc_addr))?;

        let chain = Self {
            config,
            version_specs,
            rpc_client,
            grpc_addr,
            rt,
            keybase,
            account: None,
        };

        Ok(chain)
    }

    fn init_light_client(&self) -> Result<Self::LightClient, Error> {
        use tendermint_light_client::types::PeerId;

        crate::time!("init_light_client");

        let peer_id: PeerId = self
            .rt
            .block_on(self.rpc_client.status())
            .map(|s| s.node_info.id)
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        let light_client = TmLightClient::from_config(&self.config, peer_id)?;

        Ok(light_client)
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

    fn id(&self) -> &ChainId {
        &self.config().id
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
    ///     - the SDK version is supported;
    ///
    /// Emits a log warning in case anything is amiss.
    /// Exits early if any health check fails, without doing any
    /// further checks.
    fn health_check(&self) -> Result<HealthCheck, Error> {
        if let Err(e) = self.block_on(do_health_check(self)) {
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
        proto_msgs: Vec<Any>,
    ) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("send_messages_and_wait_commit");
        debug!(
            "send_messages_and_wait_commit with {} messages",
            proto_msgs.len()
        );

        if proto_msgs.is_empty() {
            return Ok(vec![]);
        }
        let mut tx_sync_results = vec![];

        let mut n = 0;
        let mut size = 0;
        let mut msg_batch = vec![];
        for msg in proto_msgs.iter() {
            msg_batch.push(msg.clone());
            let mut buf = Vec::new();
            prost::Message::encode(msg, &mut buf).unwrap();
            n += 1;
            size += buf.len();
            if n >= self.max_msg_num() || size >= self.max_tx_size() {
                let events_per_tx = vec![IbcEvent::default(); msg_batch.len()];
                let tx_sync_result = self.send_tx(msg_batch)?;
                tx_sync_results.push(TxSyncResult {
                    response: tx_sync_result,
                    events: events_per_tx,
                });
                n = 0;
                size = 0;
                msg_batch = vec![];
            }
        }
        if !msg_batch.is_empty() {
            let events_per_tx = vec![IbcEvent::default(); msg_batch.len()];
            let tx_sync_result = self.send_tx(msg_batch)?;
            tx_sync_results.push(TxSyncResult {
                response: tx_sync_result,
                events: events_per_tx,
            });
        }

        let tx_sync_results = self.wait_for_block_commits(tx_sync_results)?;

        let events = tx_sync_results
            .into_iter()
            .map(|el| el.events)
            .flatten()
            .collect();

        Ok(events)
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        proto_msgs: Vec<Any>,
    ) -> Result<Vec<Response>, Error> {
        crate::time!("send_messages_and_wait_check_tx");
        debug!(
            "send_messages_and_wait_check_tx with {} messages",
            proto_msgs.len()
        );

        if proto_msgs.is_empty() {
            return Ok(vec![]);
        }
        let mut responses = vec![];

        let mut n = 0;
        let mut size = 0;
        let mut msg_batch = vec![];
        for msg in proto_msgs.iter() {
            msg_batch.push(msg.clone());
            let mut buf = Vec::new();
            prost::Message::encode(msg, &mut buf).unwrap();
            n += 1;
            size += buf.len();
            if n >= self.max_msg_num() || size >= self.max_tx_size() {
                // Send the tx and enqueue the resulting response
                responses.push(self.send_tx(msg_batch)?);
                n = 0;
                size = 0;
                msg_batch = vec![];
            }
        }
        if !msg_batch.is_empty() {
            responses.push(self.send_tx(msg_batch)?);
        }

        Ok(responses)
    }

    /// Get the account for the signer
    fn get_signer(&mut self) -> Result<Signer, Error> {
        crate::time!("get_signer");

        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)?;

        let bech32 = encode_to_bech32(&key.address.to_hex(), &self.config.account_prefix)?;
        Ok(Signer::new(bech32))
    }

    /// Get the chain configuration
    fn config(&self) -> ChainConfig {
        self.config.clone()
    }

    /// Get the signing key
    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        crate::time!("get_key");

        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)?;

        Ok(key)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        crate::time!("query_commitment_prefix");

        // TODO - do a real chain query
        Ok(CommitmentPrefix::from(
            self.config().store_prefix.as_bytes().to_vec(),
        ))
    }

    /// Query the chain status
    fn query_status(&self) -> Result<StatusResponse, Error> {
        crate::time!("query_status");
        let status = self.status()?;

        let time = DateTime::from(status.sync_info.latest_block_time);
        let height = ICSHeight {
            revision_number: ChainId::chain_version(status.node_info.network.as_str()),
            revision_height: u64::from(status.sync_info.latest_block_height),
        };

        Ok(StatusResponse {
            height,
            timestamp: Timestamp::from_datetime(time),
        })
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        crate::time!("query_clients");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);
        let response = self
            .block_on(client.client_states(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        // Deserialize into domain type
        let mut clients: Vec<IdentifiedAnyClientState> = response
            .client_states
            .into_iter()
            .filter_map(|cs| IdentifiedAnyClientState::try_from(cs).ok())
            .collect();

        // Sort by client identifier counter
        clients.sort_by_cached_key(|c| client_id_suffix(&c.client_id).unwrap_or(0));

        Ok(clients)
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<Self::ClientState, Error> {
        crate::time!("query_client_state");

        let client_state = self
            .query(ClientStatePath(client_id.clone()), height, false)
            .and_then(|v| AnyClientState::decode_vec(&v.value).map_err(Error::decode))?;
        let client_state = downcast!(client_state.clone() => AnyClientState::Tendermint)
            .ok_or_else(|| Error::client_state_type(format!("{:?}", client_state)))?;
        Ok(client_state)
    }

    fn query_upgraded_client_state(
        &self,
        height: ICSHeight,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        crate::time!("query_upgraded_client_state");

        // Query for the value and the proof.
        let tm_height = Height::try_from(height.revision_height).map_err(Error::invalid_height)?;
        let (upgraded_client_state_raw, proof) = self.query_client_upgrade_state(
            ClientUpgradePath::UpgradedClientState(height.revision_height),
            tm_height,
        )?;

        let client_state = AnyClientState::decode_vec(&upgraded_client_state_raw)
            .map_err(Error::conversion_from_any)?;

        let client_type = client_state.client_type();
        let tm_client_state = downcast!(client_state => AnyClientState::Tendermint)
            .ok_or_else(|| Error::client_type_mismatch(ClientType::Tendermint, client_type))?;

        Ok((tm_client_state, proof))
    }

    fn query_upgraded_consensus_state(
        &self,
        height: ICSHeight,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        crate::time!("query_upgraded_consensus_state");

        let tm_height = Height::try_from(height.revision_height).map_err(Error::invalid_height)?;

        // Fetch the consensus state and its proof.
        let (upgraded_consensus_state_raw, proof) = self.query_client_upgrade_state(
            ClientUpgradePath::UpgradedClientConsensusState(height.revision_height),
            tm_height,
        )?;

        let consensus_state = AnyConsensusState::decode_vec(&upgraded_consensus_state_raw)
            .map_err(Error::conversion_from_any)?;

        let cs_client_type = consensus_state.client_type();
        let tm_consensus_state = downcast!(consensus_state => AnyConsensusState::Tendermint)
            .ok_or_else(|| {
                Error::consensus_state_type_mismatch(ClientType::Tendermint, cs_client_type)
            })?;

        Ok((tm_consensus_state, proof))
    }

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        crate::time!("query_consensus_states");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);
        let response = self
            .block_on(client.consensus_states(request))
            .map_err(Error::grpc_status)?
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
        crate::time!("query_consensus_state");

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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = match self.block_on(client.client_connections(request)) {
            Ok(res) => res.into_inner(),
            Err(e) if e.code() == tonic::Code::NotFound => return Ok(vec![]),
            Err(e) => return Err(Error::grpc_status(e)),
        };

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
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        crate::time!("query_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(
                    self.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.connections(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        // TODO: add warnings for any identifiers that fail to parse (below).
        //      similar to the parsing in `query_connection_channels`.

        let connections = response
            .connections
            .into_iter()
            .filter_map(|co| IdentifiedConnectionEnd::try_from(co).ok())
            .collect();

        Ok(connections)
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
                    .map_err(Error::grpc_transport)?;

            let mut request = connection::QueryConnectionRequest {
                connection_id: connection_id.to_string(),
            }
            .into_request();

            let height_param = MetadataValue::from_str(&height.revision_height.to_string())
                .map_err(Error::invalid_metadata)?;

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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.connection_channels(request))
            .map_err(Error::grpc_status)?
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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.channels(request))
            .map_err(Error::grpc_status)?
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
        let channel_end = ChannelEnd::decode_vec(&res.value).map_err(Error::decode)?;

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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.channel_client_state(request))
            .map_err(Error::grpc_status)?
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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.packet_commitments(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let mut pc = response.commitments;
        pc.sort_by_key(|ps| ps.sequence);

        let height = response
            .height
            .ok_or_else(|| Error::grpc_response_param("height".to_string()))?
            .into();

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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let mut response = self
            .block_on(client.unreceived_packets(request))
            .map_err(Error::grpc_status)?
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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.packet_acknowledgements(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let pc = response.acknowledgements;

        let height = response
            .height
            .ok_or_else(|| Error::grpc_response_param("height".to_string()))?
            .into();

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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let mut response = self
            .block_on(client.unreceived_acks(request))
            .map_err(Error::grpc_status)?
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
            .map_err(Error::grpc_transport)?;

        let request = tonic::Request::new(request);

        let response = self
            .block_on(client.next_sequence_receive(request))
            .map_err(Error::grpc_status)?
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
                        .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

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
                    .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

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

            QueryTxRequest::Transaction(tx) => {
                let mut response = self
                    .block_on(self.rpc_client.tx_search(
                        tx_hash_query(&tx),
                        false,
                        1,
                        1, // get only the first Tx matching the query
                        Order::Ascending,
                    ))
                    .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

                if response.txs.is_empty() {
                    Ok(vec![])
                } else {
                    let tx = response.txs.remove(0);
                    Ok(all_ibc_events_from_tx_search_response(self.id(), tx))
                }
            }
        }
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        crate::time!("query_blocks");

        match request {
            QueryBlockRequest::Packet(request) => {
                crate::time!("query_blocks: query block packet events");

                let mut begin_block_events: Vec<IbcEvent> = vec![];
                let mut end_block_events: Vec<IbcEvent> = vec![];

                for seq in &request.sequences {
                    let response = self
                        .block_on(self.rpc_client.block_search(
                            packet_query(&request, *seq),
                            1,
                            1, // there should only be a single match for this query
                            Order::Ascending,
                        ))
                        .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

                    assert!(
                        response.blocks.len() <= 1,
                        "block_results: unexpected number of blocks"
                    );

                    if let Some(block) = response.blocks.first().map(|first| &first.block) {
                        let response_height =
                            ICSHeight::new(self.id().version(), u64::from(block.header.height));
                        if request.height != ICSHeight::zero() && response_height > request.height {
                            continue;
                        }
                        let response = self
                            .block_on(self.rpc_client.block_results(block.header.height))
                            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

                        begin_block_events.append(
                            &mut response
                                .begin_block_events
                                .unwrap_or_default()
                                .into_iter()
                                .filter_map(|ev| filter_matching_event(ev, &request, *seq))
                                .collect(),
                        );

                        end_block_events.append(
                            &mut response
                                .end_block_events
                                .unwrap_or_default()
                                .into_iter()
                                .filter_map(|ev| filter_matching_event(ev, &request, *seq))
                                .collect(),
                        );
                    }
                }
                Ok((begin_block_events, end_block_events))
            }
        }
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        crate::time!("proven_client_state");

        let res = self.query(ClientStatePath(client_id.clone()), height, true)?;

        let client_state = AnyClientState::decode_vec(&res.value).map_err(Error::decode)?;

        let client_state = downcast!(client_state.clone() => AnyClientState::Tendermint)
            .ok_or_else(|| Error::client_state_type(format!("{:?}", client_state)))?;

        Ok((
            client_state,
            res.proof.ok_or_else(Error::empty_response_proof)?,
        ))
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: ICSHeight,
        height: ICSHeight,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        crate::time!("proven_client_consensus");

        let res = self.query(
            ClientConsensusPath {
                client_id: client_id.clone(),
                epoch: consensus_height.revision_number,
                height: consensus_height.revision_height,
            },
            height,
            true,
        )?;

        let consensus_state = AnyConsensusState::decode_vec(&res.value).map_err(Error::decode)?;

        let consensus_state =
            downcast!(consensus_state.clone() => AnyConsensusState::Tendermint)
                .ok_or_else(|| Error::client_state_type(format!("{:?}", consensus_state)))?;

        Ok((
            consensus_state,
            res.proof.ok_or_else(Error::empty_response_proof)?,
        ))
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        let res = self.query(Path::Connections(connection_id.clone()), height, true)?;
        let connection_end = ConnectionEnd::decode_vec(&res.value).map_err(Error::decode)?;

        Ok((
            connection_end,
            res.proof.ok_or_else(Error::empty_response_proof)?,
        ))
    }

    fn proven_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<(ChannelEnd, MerkleProof), Error> {
        let res = self.query(
            Path::ChannelEnds(port_id.clone(), channel_id.clone()),
            height,
            true,
        )?;

        let channel_end = ChannelEnd::decode_vec(&res.value).map_err(Error::decode)?;

        Ok((
            channel_end,
            res.proof.ok_or_else(Error::empty_response_proof)?,
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

        let res = self.query(data, height, true)?;

        let commitment_proof_bytes = res.proof.ok_or_else(Error::empty_response_proof)?;

        Ok((res.value, commitment_proof_bytes))
    }

    fn build_client_state(
        &self,
        height: ICSHeight,
        dst_config: ChainConfig,
    ) -> Result<Self::ClientState, Error> {
        let unbonding_period = self.unbonding_period()?;

        let max_clock_drift = calculate_client_state_drift(self.config(), &dst_config);

        // Build the client state.
        ClientState::new(
            self.id().clone(),
            self.config.trust_threshold.into(),
            self.trusting_period(unbonding_period),
            unbonding_period,
            max_clock_drift,
            height,
            ICSHeight::zero(),
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
        &self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
        light_client: &mut Self::LightClient,
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

fn tx_hash_query(request: &QueryTxHash) -> Query {
    tendermint_rpc::query::Query::eq("tx.hash", request.0.to_string())
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
        .filter_map(|ev| filter_matching_event(ev, request, seq))
        .next()
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
            IbcEvent::UpdateClient(mut update) => {
                update.common.height = height;
                Some(update)
            }
            _ => None,
        })
        .find(|update| {
            update.common.client_id == request.client_id
                && update.common.consensus_height == request.consensus_height
        })
        .map(IbcEvent::UpdateClient)
}

fn all_ibc_events_from_tx_search_response(chain_id: &ChainId, response: ResultTx) -> Vec<IbcEvent> {
    let height = ICSHeight::new(chain_id.version(), u64::from(response.height));
    let deliver_tx_result = response.tx_result;
    if deliver_tx_result.code.is_err() {
        return vec![IbcEvent::ChainError(format!(
            "deliver_tx for {} reports error: code={:?}, log={:?}",
            response.hash, deliver_tx_result.code, deliver_tx_result.log
        ))];
    }

    let mut result = vec![];
    for event in deliver_tx_result.events {
        if let Some(ibc_ev) = from_tx_response_event(height, &event) {
            result.push(ibc_ev);
        }
    }
    result
}

fn filter_matching_event(
    event: Event,
    request: &QueryPacketEventDataRequest,
    seq: Sequence,
) -> Option<IbcEvent> {
    fn matches_packet(
        request: &QueryPacketEventDataRequest,
        seq: Sequence,
        packet: &Packet,
    ) -> bool {
        packet.source_port == request.source_port_id
            && packet.source_channel == request.source_channel_id
            && packet.destination_port == request.destination_port_id
            && packet.destination_channel == request.destination_channel_id
            && packet.sequence == seq
    }

    if event.type_str != request.event_id.as_str() {
        return None;
    }

    let ibc_event = ChannelEvents::try_from_tx(&event)?;
    match ibc_event {
        IbcEvent::SendPacket(ref send_ev) if matches_packet(request, seq, &send_ev.packet) => {
            Some(ibc_event)
        }
        IbcEvent::WriteAcknowledgement(ref ack_ev)
            if matches_packet(request, seq, &ack_ev.packet) =>
        {
            Some(ibc_event)
        }
        _ => None,
    }
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
        .map_err(|e| Error::rpc(chain.config.rpc_addr.clone(), e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        return Err(Error::abci_query(response));
    }

    if prove && response.proof.is_none() {
        // Fail due to empty proof
        return Err(Error::empty_response_proof());
    }

    let proof = response
        .proof
        .map(|p| convert_tm_to_ics_merkle_proof(&p))
        .transpose()
        .map_err(Error::ics23)?;

    let response = QueryResponse {
        value: response.value,
        height: response.height,
        proof,
    };

    Ok(response)
}

/// Perform a `broadcast_tx_sync`, and return the corresponding deserialized response data.
async fn broadcast_tx_sync(chain: &CosmosSdkChain, data: Vec<u8>) -> Result<Response, Error> {
    let response = chain
        .rpc_client()
        .broadcast_tx_sync(data.into())
        .await
        .map_err(|e| Error::rpc(chain.config.rpc_addr.clone(), e))?;

    Ok(response)
}

/// Uses the GRPC client to retrieve the account sequence
async fn query_account(chain: &CosmosSdkChain, address: String) -> Result<BaseAccount, Error> {
    let mut client = ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient::connect(
        chain.grpc_addr.clone(),
    )
    .await
    .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(QueryAccountRequest { address });

    let response = client.account(request).await;
    let resp_account = response
        .map_err(Error::grpc_status)?
        .into_inner()
        .account
        .unwrap();
    if resp_account.type_url == "/cosmos.auth.v1beta1.BaseAccount" {
        Ok(BaseAccount::decode(resp_account.value.as_slice())
            .map_err(|e| Error::protobuf_decode("BaseAccount".to_string(), e))?)
    } else if resp_account.type_url.ends_with(".EthAccount") {
        Ok(EthAccount::decode(resp_account.value.as_slice())
            .map_err(|e| Error::protobuf_decode("EthAccount".to_string(), e))?
            .base_account
            .ok_or_else(Error::empty_base_account)?)
    } else {
        Err(Error::unknown_account_type(resp_account.type_url))
    }
}

fn encode_to_bech32(address: &str, account_prefix: &str) -> Result<String, Error> {
    let account = AccountId::from_str(address)
        .map_err(|e| Error::invalid_key_address(address.to_string(), e))?;

    let encoded = bech32::encode(account_prefix, account.to_base32(), Variant::Bech32)
        .map_err(Error::bech32_encoding)?;

    Ok(encoded)
}

/// Returns the suffix counter for a CosmosSDK client id.
/// Returns `None` if the client identifier is malformed
/// and the suffix could not be parsed.
fn client_id_suffix(client_id: &ClientId) -> Option<u64> {
    client_id
        .as_str()
        .split('-')
        .last()
        .map(|e| e.parse::<u64>().ok())
        .flatten()
}

pub struct TxSyncResult {
    // the broadcast_tx_sync response
    response: Response,
    // the events generated by a Tx once executed
    events: Vec<IbcEvent>,
}

fn auth_info_and_bytes(signer_info: SignerInfo, fee: Fee) -> Result<(AuthInfo, Vec<u8>), Error> {
    let auth_info = AuthInfo {
        signer_infos: vec![signer_info],
        fee: Some(fee),
    };

    // A protobuf serialization of a AuthInfo
    let mut auth_buf = Vec::new();
    prost::Message::encode(&auth_info, &mut auth_buf).unwrap();
    Ok((auth_info, auth_buf))
}

fn tx_body_and_bytes(proto_msgs: Vec<Any>, memo: &Memo) -> Result<(TxBody, Vec<u8>), Error> {
    // Create TxBody
    let body = TxBody {
        messages: proto_msgs.to_vec(),
        memo: memo.to_string(),
        timeout_height: 0_u64,
        extension_options: Vec::<Any>::new(),
        non_critical_extension_options: Vec::<Any>::new(),
    };

    // A protobuf serialization of a TxBody
    let mut body_buf = Vec::new();
    prost::Message::encode(&body, &mut body_buf).unwrap();
    Ok((body, body_buf))
}

async fn do_health_check(chain: &CosmosSdkChain) -> Result<(), Error> {
    let chain_id = chain.id();
    let grpc_address = chain.grpc_addr.to_string();
    let rpc_address = chain.config.rpc_addr.to_string();

    // Checkup on the self-reported health endpoint
    chain.rpc_client.health().await.map_err(|e| {
        Error::health_check_json_rpc(
            chain_id.clone(),
            rpc_address.clone(),
            "/health".to_string(),
            e,
        )
    })?;

    // Checkup on transaction indexing
    chain
        .rpc_client
        .tx_search(
            Query::from(EventType::NewBlock),
            false,
            1,
            1,
            Order::Ascending,
        )
        .await
        .map_err(|e| {
            Error::health_check_json_rpc(
                chain_id.clone(),
                rpc_address.clone(),
                "/tx_search".to_string(),
                e,
            )
        })?;

    // Checkup on the underlying SDK & IBC-go versions
    if let Err(diagnostic) = compatibility::run_diagnostic(&chain.version_specs) {
        return Err(Error::sdk_module_version(
            chain_id.clone(),
            grpc_address.clone(),
            diagnostic.to_string(),
        ));
    }

    Ok(())
}

/// Queries the chain to obtain the version information.
async fn fetch_version_specs(
    chain_id: &ChainId,
    grpc_address: &Uri,
) -> Result<version::Specs, Error> {
    let grpc_addr_string = grpc_address.to_string();

    // Construct a gRPC client
    let mut client = ServiceClient::connect(grpc_address.clone())
        .await
        .map_err(|e| {
            Error::fetch_version_grpc_transport(
                chain_id.clone(),
                grpc_addr_string.clone(),
                "tendermint::ServiceClient".to_string(),
                e,
            )
        })?;

    let request = tonic::Request::new(GetNodeInfoRequest {});

    let response = client.get_node_info(request).await.map_err(|e| {
        Error::fetch_version_grpc_status(
            chain_id.clone(),
            grpc_addr_string.clone(),
            "tendermint::ServiceClient".to_string(),
            e,
        )
    })?;

    let version = response.into_inner().application_version.ok_or_else(|| {
        Error::fetch_version_invalid_version_response(
            chain_id.clone(),
            grpc_addr_string.clone(),
            "tendermint::GetNodeInfoRequest".to_string(),
        )
    })?;

    // Parse the raw version info into a domain-type `version::Specs`
    version
        .try_into()
        .map_err(|e| Error::fetch_version_parsing(chain_id.clone(), grpc_addr_string.clone(), e))
}

struct PrettyFee<'a>(&'a Fee);

impl fmt::Display for PrettyFee<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let amount = match self.0.amount.get(0) {
            Some(coin) => format!("{}{}", coin.amount, coin.denom),
            None => "<no amount specified>".to_string(),
        };

        f.debug_struct("Fee")
            .field("amount", &amount)
            .field("gas_limit", &self.0.gas_limit)
            .finish()
    }
}

fn calculate_fee(adjusted_gas_amount: u64, gas_price: &GasPrice) -> Coin {
    let fee_amount = mul_ceil(adjusted_gas_amount, gas_price.price);

    Coin {
        denom: gas_price.denom.to_string(),
        amount: fee_amount.to_string(),
    }
}

/// Multiply `a` with `f` and round to result up to the nearest integer.
fn mul_ceil(a: u64, f: f64) -> u64 {
    use fraction::Fraction as F;

    // Safe to unwrap below as are multiplying two finite fractions
    // together, and rounding them to the nearest integer.
    let n = (F::from(a) * F::from(f)).ceil();
    n.numer().unwrap() / n.denom().unwrap()
}

/// Compute the `max_clock_drift` for a (new) client state
/// as a function of the configuration of the source chain
/// and the destination chain configuration.
///
/// The client state clock drift must account for destination
/// chain block frequency and clock drift on source and dest.
/// https://github.com/informalsystems/ibc-rs/issues/1445
fn calculate_client_state_drift(
    src_chain_config: &ChainConfig,
    dst_chain_config: &ChainConfig,
) -> Duration {
    src_chain_config.clock_drift + dst_chain_config.clock_drift + dst_chain_config.max_block_time
}

#[cfg(test)]
mod tests {
    use ibc::{
        core::{
            ics02_client::client_state::{AnyClientState, IdentifiedAnyClientState},
            ics02_client::client_type::ClientType,
            ics24_host::identifier::ClientId,
        },
        mock::client_state::MockClientState,
        mock::header::MockHeader,
        Height,
    };

    use crate::chain::cosmos::client_id_suffix;

    #[test]
    fn mul_ceil() {
        assert_eq!(super::mul_ceil(300_000, 0.001), 300);
        assert_eq!(super::mul_ceil(300_004, 0.001), 301);
        assert_eq!(super::mul_ceil(300_040, 0.001), 301);
        assert_eq!(super::mul_ceil(300_400, 0.001), 301);
        assert_eq!(super::mul_ceil(304_000, 0.001), 304);
        assert_eq!(super::mul_ceil(340_000, 0.001), 340);
        assert_eq!(super::mul_ceil(340_001, 0.001), 341);
    }

    #[test]
    fn sort_clients_id_suffix() {
        let mut clients: Vec<IdentifiedAnyClientState> = vec![
            IdentifiedAnyClientState::new(
                ClientId::new(ClientType::Tendermint, 4).unwrap(),
                AnyClientState::Mock(MockClientState(MockHeader::new(Height::new(0, 0)))),
            ),
            IdentifiedAnyClientState::new(
                ClientId::new(ClientType::Tendermint, 1).unwrap(),
                AnyClientState::Mock(MockClientState(MockHeader::new(Height::new(0, 0)))),
            ),
            IdentifiedAnyClientState::new(
                ClientId::new(ClientType::Tendermint, 7).unwrap(),
                AnyClientState::Mock(MockClientState(MockHeader::new(Height::new(0, 0)))),
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
