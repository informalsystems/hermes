//! Cardano ChainEndpoint implementation for Hermes
//!
//! This module implements the ChainEndpoint trait required by Hermes for custom chain support.

use super::config::CardanoConfig;
use super::gateway_client::GatewayClient;
use super::signing_key_pair::CardanoSigningKeyPair;

use ibc_relayer_types::clients::ics08_cardano::header::Header as MithrilHeader;
use ibc_relayer_types::clients::ics08_cardano::{
    client_state::ClientState as MithrilClientState,
    consensus_state::ConsensusState as MithrilConsensusState,
};

use crate::account::Balance;
use crate::chain::client::ClientSettings;
use crate::chain::cosmos::version::Specs as CosmosSpecs;
use crate::chain::endpoint::{ChainEndpoint, ChainStatus, HealthCheck};
use crate::chain::handle::Subscription;
use crate::chain::requests::{
    CrossChainQueryRequest, IncludeProof, QueryChannelClientStateRequest, QueryChannelRequest,
    QueryChannelsRequest, QueryClientConnectionsRequest, QueryClientStateRequest,
    QueryClientStatesRequest, QueryConnectionChannelsRequest, QueryConnectionRequest,
    QueryConnectionsRequest, QueryConsensusStateHeightsRequest, QueryConsensusStateRequest,
    QueryHostConsensusStateRequest, QueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentRequest, QueryPacketCommitmentsRequest, QueryPacketEventDataRequest,
    QueryPacketReceiptRequest, QueryTxRequest, QueryUnreceivedAcksRequest,
    QueryUnreceivedPacketsRequest, QueryUpgradedClientStateRequest,
    QueryUpgradedConsensusStateRequest,
};
use crate::chain::tracking::TrackedMsgs;
use crate::chain::version::Specs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::{ChainConfig, Error as ConfigError};
use crate::consensus_state::AnyConsensusState;
use crate::denom::DenomTrace;
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::keyring::{KeyRing, SigningKeyPair};
use crate::misbehaviour::MisbehaviourEvidence;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentRoot;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height as ICSHeight;
use std::str::FromStr;
use std::sync::Arc;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response as TxResponse;
use tokio::runtime::Runtime as TokioRuntime;

/// Cardano light block (placeholder)
#[derive(Debug, Clone)]
pub struct CardanoLightBlock {
    pub header: MithrilHeader,
    pub host_state_nft_policy_id: Vec<u8>,
    pub host_state_nft_token_name: Vec<u8>,
}

// CardanoSigningKeyPair is now defined in signing_key_pair.rs
// From<CardanoSigningKeyPair> for AnySigningKeyPair is implemented in ibc-relayer/src/keyring/any_signing_key_pair.rs

/// Cardano ChainEndpoint implementation
pub struct CardanoChainEndpoint {
    config: CardanoConfig,
    rt: Arc<TokioRuntime>,
    gateway_client: GatewayClient,
    keyring: KeyRing<CardanoSigningKeyPair>,
    event_source_cmd: Option<crate::event::source::TxEventSourceCmd>,
}

impl CardanoChainEndpoint {
    /// Sign a transaction using the keyring (private helper method)
    fn sign_transaction_helper(&self, unsigned_cbor_hex: &str) -> Result<String, Error> {
        use super::signer;

        // Convert hex to bytes
        let unsigned_tx_bytes = hex::decode(unsigned_cbor_hex)
            .map_err(|e| Error::send_tx(format!("Failed to decode unsigned tx hex: {}", e)))?;

        // Get signing key from keyring
        let key = self
            .keyring
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)?;

        // Get the CardanoSigningKeyPair and extract the CardanoKeyring
        let signing_key_pair = key
            .as_any()
            .downcast_ref::<CardanoSigningKeyPair>()
            .ok_or_else(|| {
                Error::send_tx("Failed to downcast to CardanoSigningKeyPair".to_string())
            })?;
        let cardano_keyring = signing_key_pair
            .get_cardano_keyring()
            .map_err(|e| Error::send_tx(format!("Failed to get CardanoKeyring: {}", e)))?;

        // Sign the transaction
        let signed_tx_bytes = signer::sign_transaction(&unsigned_tx_bytes, &cardano_keyring)
            .map_err(|e| Error::send_tx(format!("Failed to sign transaction: {}", e)))?;

        // Convert back to hex
        Ok(hex::encode(signed_tx_bytes))
    }

    /// Initialize the event source for monitoring Cardano chain events
    fn init_event_source(&mut self) -> Result<crate::event::source::TxEventSourceCmd, Error> {
        use super::event_source::CardanoEventSource;
        use std::thread;
        use std::time::Duration;

        tracing::info!("Initializing Cardano event source with polling");

        // Get poll interval from config (default 5 seconds)
        let poll_interval = self
            .config
            .event_poll_interval
            .unwrap_or_else(|| Duration::from_secs(5));

        let (event_source, monitor_tx) = CardanoEventSource::new(
            self.config.id.clone(),
            self.gateway_client.clone(),
            poll_interval,
            self.rt.clone(),
        )
        .map_err(Error::event_source)?;

        thread::spawn(move || event_source.run());

        tracing::info!(
            "Event source initialized, polling every {:?}",
            poll_interval
        );

        Ok(monitor_tx)
    }

    /// Wait until the Gateway's "latest height" has caught up to (or passed) a specific
    /// Cardano transaction inclusion height.
    ///
    /// Why this exists:
    /// - The Gateway returns a transaction `height` in `submit_signed_tx` based on `db-sync`'s
    ///   `block_no` for the block that included the transaction.
    /// - Separately, for Cardano↔Cosmos IBC, the Cosmos-side light client only accepts *Mithril-
    ///   certified* heights. In this integration, we treat the IBC `Height.revision_height` for
    ///   Cardano as the Mithril Cardano-transactions snapshot `block_number` (a monotonically
    ///   increasing block number), not as the raw chain tip.
    ///
    /// If Hermes proceeds immediately after inclusion, it may query proofs at a height that the
    /// Cosmos-side client has not yet been updated to, or worse: it may receive proofs that are
    /// valid for a newer on-chain HostState root but are being verified against an older certified
    /// root. That shows up as "proof does not match ibc_state_root".
    ///
    /// To avoid this class of race, we treat "commit" for Cardano transactions as "included AND
    /// covered by the latest Mithril transaction snapshot".
    async fn wait_for_mithril_certified_height(
        &self,
        included_height: ICSHeight,
    ) -> Result<ICSHeight, Error> {
        let poll_interval = self.config.mithril_poll_interval;
        let timeout = self.config.mithril_certification_timeout;
        let log_interval = self.config.mithril_wait_log_interval;
        let start = tokio::time::Instant::now();
        let mut last_logged_elapsed = std::time::Duration::from_secs(0);
        let mut last_latest_height: Option<u64> = None;

        loop {
            let latest = self
                .gateway_client
                .query_latest_height()
                .await
                .map_err(|e| Error::query(format!("Gateway query_latest_height failed: {e}")))?;

            if latest.revision_number() != included_height.revision_number() {
                return Err(Error::query(format!(
                    "gateway returned revision_number={} but expected revision_number={}",
                    latest.revision_number(),
                    included_height.revision_number()
                )));
            }

            if latest.revision_height() >= included_height.revision_height() {
                return Ok(latest);
            }

            let elapsed = start.elapsed();
            if elapsed >= timeout {
                return Err(Error::send_tx(format!(
                    "timed out waiting for Mithril-certified height >= {} (latest={}). \
                     Note: for Cardano, Height.revision_height is a Mithril snapshot block_number (not a slot).",
                    included_height, latest,
                )));
            }

            let latest_height = latest.revision_height();
            let required_height = included_height.revision_height();
            let missing_blocks = required_height.saturating_sub(latest_height);

            let latest_changed = last_latest_height
                .map(|prev| prev != latest_height)
                .unwrap_or(true);
            let should_log =
                latest_changed || elapsed.saturating_sub(last_logged_elapsed) >= log_interval;

            if should_log {
                let remaining = timeout.saturating_sub(elapsed);
                let log_msg = format!(
                    "Waiting for Mithril snapshot: need >= {} (missing {} blocks), have {}, elapsed={}s, remaining={}s",
                    included_height,
                    missing_blocks,
                    latest,
                    elapsed.as_secs(),
                    remaining.as_secs(),
                );

                if remaining <= log_interval {
                    tracing::warn!("{log_msg}");
                } else {
                    tracing::info!("{log_msg}");
                }

                last_logged_elapsed = elapsed;
            }

            last_latest_height = Some(latest_height);
            tokio::time::sleep(poll_interval).await;
        }
    }
}

impl ChainEndpoint for CardanoChainEndpoint {
    type LightBlock = CardanoLightBlock;
    type Header = MithrilHeader;
    type ConsensusState = MithrilConsensusState;
    type ClientState = MithrilClientState;
    type Time = i64; // Unix timestamp
    type SigningKeyPair = CardanoSigningKeyPair;

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn config(&self) -> ChainConfig {
        ChainConfig::Cardano(self.config.clone())
    }

    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error> {
        tracing::info!("Bootstrapping Cardano chain endpoint");

        // Extract Cardano-specific config
        let cardano_config: CardanoConfig = match config {
            ChainConfig::Cardano(config) => config,
            _ => {
                tracing::error!("Invalid config type provided to Cardano bootstrap");
                return Err(Error::config(ConfigError::wrong_type()));
            }
        };

        tracing::info!(
            "Initializing Cardano endpoint for chain: {}, gateway: {}",
            cardano_config.id,
            cardano_config.gateway_url
        );

        // Initialize Gateway client (async operation, so use rt.block_on)
        let gateway_client = rt
            .block_on(GatewayClient::new(cardano_config.gateway_url.clone()))
            .map_err(|e| {
                tracing::error!("Failed to initialize Gateway client: {}", e);
                Error::config(ConfigError::wrong_type())
            })?;

        tracing::info!("Gateway client initialized successfully");

        // Initialize keyring
        // Note: Cardano uses "addr" as account prefix (similar to how Cosmos uses prefixes)
        let keyring = KeyRing::new(
            cardano_config.key_store_type,
            "addr", // Cardano address prefix
            &cardano_config.id,
            &cardano_config.key_store_folder,
        )
        .map_err(Error::key_base)?;

        tracing::info!("Keyring initialized successfully");

        let endpoint = Self {
            config: cardano_config,
            rt,
            gateway_client,
            keyring,
            event_source_cmd: None, // Initialized lazily on first subscribe() call
        };

        tracing::info!("Cardano chain endpoint bootstrap complete");
        Ok(endpoint)
    }

    fn shutdown(self) -> Result<(), Error> {
        tracing::info!("Shutting down Cardano chain endpoint");
        Ok(())
    }

    fn health_check(&mut self) -> Result<HealthCheck, Error> {
        match self.rt.block_on(self.gateway_client.query_latest_height()) {
            Ok(_) => Ok(HealthCheck::Healthy),
            Err(e) => Ok(HealthCheck::Unhealthy(Box::new(Error::query(format!(
                "Gateway health check failed: {e}"
            ))))),
        }
    }

    fn subscribe(&mut self) -> Result<Subscription, Error> {
        if self.event_source_cmd.is_none() {
            self.event_source_cmd = Some(self.init_event_source()?);
        }

        let event_source_cmd = self.event_source_cmd.as_ref().ok_or_else(|| {
            Error::event_source(crate::event::source::Error::collect_events_failed(
                "Cardano event source command missing after initialization".to_string(),
            ))
        })?;

        let subscription = event_source_cmd.subscribe().map_err(Error::event_source)?;
        Ok(subscription)
    }

    fn keybase(&self) -> &KeyRing<Self::SigningKeyPair> {
        &self.keyring
    }

    fn keybase_mut(&mut self) -> &mut KeyRing<Self::SigningKeyPair> {
        &mut self.keyring
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        let key = self
            .keyring
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)?;

        let cardano_keyring = key.get_cardano_keyring().map_err(Error::key_base)?;
        let address = cardano_keyring.address(self.config.network_id);

        Signer::from_str(&address).map_err(|e| {
            Error::key_base(crate::keyring::errors::Error::invalid_mnemonic(
                anyhow::anyhow!("Invalid signer address: {e}"),
            ))
        })
    }

    fn get_key(&self) -> Result<Self::SigningKeyPair, Error> {
        // Get the signing key pair from keyring
        self.keyring
            .get_key(&self.config.key_name)
            .map_err(Error::key_base)
    }

    fn version_specs(&self) -> Result<Specs, Error> {
        // TODO: Return Cardano version info
        // Return empty Cosmos specs for now (Cardano doesn't use Cosmos SDK)
        Ok(Specs::Cosmos(CosmosSpecs {
            cosmos_sdk: None,
            ibc_go: None,
            consensus: None,
        }))
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        tracing::info!(
            "send_messages_and_wait_commit: processing {} messages",
            tracked_msgs.msgs.len()
        );

        // Block on async operations using the runtime
        self.rt.block_on(async {
            let mut all_events = Vec::new();

            for msg in tracked_msgs.msgs.iter() {
                tracing::debug!("Processing message type: {:?}", msg.type_url);

                // Step 1: Build unsigned transaction via Gateway
                let unsigned_tx = self
                    .gateway_client
                    .build_ibc_tx(&msg.type_url, msg.value.clone())
                    .await
                    .map_err(|e| Error::send_tx(format!("Failed to build transaction: {}", e)))?;

                tracing::debug!("Built unsigned tx: {}", unsigned_tx.description);

                // Step 2: Sign transaction with keyring
                let signed_cbor_hex = self.sign_transaction_helper(&unsigned_tx.cbor_hex)?;

                tracing::debug!("Signed transaction, CBOR length: {}", signed_cbor_hex.len());

                // Step 3: Submit signed transaction via Gateway
                let tx_response = self
                    .gateway_client
                    .submit_signed_tx(&signed_cbor_hex)
                    .await
                    .map_err(|e| Error::send_tx(format!("Failed to submit transaction: {}", e)))?;

                let tx_hash = tx_response.tx_hash.clone();
                let event_count = tx_response.events.len();

                if event_count == 0 {
                    tracing::warn!("Transaction {} produced no gateway events", tx_hash);
                } else {
                    tracing::info!(
                        "Transaction {} produced {} gateway events",
                        tx_hash,
                        event_count
                    );
                    tracing::debug!(
                        "Gateway events for {}: {:?}",
                        tx_hash,
                        tx_response
                            .events
                            .iter()
                            .map(|event| event.event_type.as_str())
                            .collect::<Vec<_>>()
                    );
                }

                // Step 4: Parse events from transaction result
                let included_height = tx_response.height.ok_or_else(|| {
                    Error::send_tx("No height in transaction response".to_string())
                })?;

                tracing::info!(
                    "Transaction submitted: {} at height {}",
                    tx_response.tx_hash,
                    included_height
                );

                // Ensure the transaction is also covered by the latest Mithril transaction snapshot
                // before we treat it as "committed" from the perspective of IBC relaying.
                let certified_height = self
                    .wait_for_mithril_certified_height(included_height)
                    .await?;
                if certified_height.revision_height() != included_height.revision_height() {
                    tracing::info!(
                        "Transaction {} inclusion height {} is now certified at {}",
                        tx_response.tx_hash,
                        included_height,
                        certified_height
                    );
                }

                // Log all events for debugging
                for event in &tx_response.events {
                    tracing::debug!(
                        "Gateway event: type={} attributes={:?}",
                        event.event_type,
                        event.attributes
                    );
                }

                // Convert custom IbcEvent to proto Event format for parsing
                let proto_events: Vec<super::generated::ibc::cardano::v1::Event> = tx_response
                    .events
                    .into_iter()
                    .map(|e| super::generated::ibc::cardano::v1::Event {
                        r#type: e.event_type,
                        attributes: e
                            .attributes
                            .into_iter()
                            .map(
                                |(k, v)| super::generated::ibc::cardano::v1::EventAttribute {
                                    key: k,
                                    value: v,
                                },
                            )
                            .collect(),
                    })
                    .collect();

                // Parse Gateway events into Hermes IbcEvent types
                let parsed_events =
                    super::event_parser::parse_events(proto_events, certified_height).map_err(
                        |e| {
                            tracing::warn!(
                                "Failed to parse IBC events from transaction {} at {}: {}",
                                tx_hash,
                                certified_height,
                                e
                            );
                            Error::send_tx(format!("Failed to parse events: {}", e))
                        },
                    )?;

                if parsed_events.is_empty() {
                    tracing::warn!(
                        "Parsed 0 IBC events from transaction {} at {}",
                        tx_hash,
                        certified_height
                    );
                } else {
                    tracing::info!(
                        "Parsed {} IBC events from transaction {}",
                        parsed_events.len(),
                        tx_hash
                    );
                }

                // Wrap events with height
                let events_with_height: Vec<IbcEventWithHeight> = parsed_events
                    .into_iter()
                    .map(|event| IbcEventWithHeight::new(event, certified_height))
                    .collect();

                // Add parsed events to result
                all_events.extend(events_with_height);
            }

            Ok(all_events)
        })
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<TxResponse>, Error> {
        tracing::info!(
            "send_messages_and_wait_check_tx: processing {} messages",
            tracked_msgs.msgs.len()
        );

        if tracked_msgs.msgs.is_empty() {
            return Ok(vec![]);
        }

        self.rt.block_on(async {
            use bytes::Bytes;
            use tendermint::abci::Code;
            use tendermint::Hash;

            let mut responses = Vec::with_capacity(tracked_msgs.msgs.len());

            for msg in tracked_msgs.msgs.iter() {
                tracing::debug!("Processing message type: {:?}", msg.type_url);

                let unsigned_tx = self
                    .gateway_client
                    .build_ibc_tx(&msg.type_url, msg.value.clone())
                    .await
                    .map_err(|e| Error::send_tx(format!("Failed to build transaction: {e}")))?;

                let signed_cbor_hex = self.sign_transaction_helper(&unsigned_tx.cbor_hex)?;

                let tx_response = self
                    .gateway_client
                    .submit_signed_tx(&signed_cbor_hex)
                    .await
                    .map_err(|e| Error::send_tx(format!("Failed to submit transaction: {e}")))?;

                let hash = match Hash::from_str(&tx_response.tx_hash.to_ascii_uppercase()) {
                    Ok(h) => h,
                    Err(e) => {
                        tracing::warn!(
                            "failed to parse tx hash `{}` as Tendermint hash: {e}",
                            tx_response.tx_hash
                        );
                        Hash::None
                    }
                };

                responses.push(TxResponse {
                    codespace: String::new(),
                    code: Code::Ok,
                    data: Bytes::new(),
                    log: format!("submitted tx {}", tx_response.tx_hash),
                    hash,
                });
            }

            Ok(responses)
        })
    }

    fn verify_header(
        &mut self,
        _trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        // Hermes uses `verify_header()` as part of its generic client update workflow.
        //
        // For Tendermint clients, this verifies signatures and header continuity off-chain.
        // For Cardano, we rely on on-chain verification in the Cosmos-side Mithril light client
        // implementation (the chain rejects invalid Mithril headers and proofs).
        //
        // To keep Hermes functional without coupling it to the full Mithril verification stack
        // (which is already implemented in the on-chain client), we treat this as a best-effort
        // fetch + structural validation step:
        // - fetch the MithrilHeader for `target` from the Gateway
        // - return it as a CardanoLightBlock so the relayer can proceed
        //
        // TODO: Implement optional off-chain verification to avoid broadcasting invalid headers and
        // wasting fees, and to enable richer relayer-side diagnostics.
        let header = self
            .rt
            .block_on(self.gateway_client.query_header(target))
            .map_err(|e| {
                Error::query(format!("failed to query Cardano header from Gateway: {e}"))
            })?;

        let (host_state_nft_policy_id, host_state_nft_token_name) = match client_state {
            AnyClientState::Mithril(state) => (
                state.host_state_nft_policy_id.clone(),
                state.host_state_nft_token_name.clone(),
            ),
            _ => {
                return Err(Error::query(
                    "Cardano verify_header requires a Mithril client state".to_string(),
                ))
            }
        };

        Ok(CardanoLightBlock {
            header,
            host_state_nft_policy_id,
            host_state_nft_token_name,
        })
    }

    fn check_misbehaviour(
        &mut self,
        _update: &UpdateClient,
        _client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        // TODO: Check for Cardano misbehaviour
        tracing::warn!("check_misbehaviour: stub implementation");
        Ok(None)
    }

    fn query_balance(&self, key_name: Option<&str>, denom: Option<&str>) -> Result<Balance, Error> {
        let denom = denom.unwrap_or("lovelace"); // Cardano's base unit
        let key_name = key_name.unwrap_or(&self.config.key_name);

        Err(Error::query(format!(
            "Cardano balance query is not implemented (key={key_name}, denom={denom}); requires Gateway UTXO/balance query support"
        )))
    }

    fn query_all_balances(&self, key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        let key_name = key_name.unwrap_or(&self.config.key_name);
        Err(Error::query(format!(
            "Cardano all-balances query is not implemented (key={key_name}); requires Gateway UTXO/balance query support"
        )))
    }

    fn query_denom_trace(&self, _hash: String) -> Result<DenomTrace, Error> {
        // Not applicable to Cardano (native assets)
        tracing::warn!("query_denom_trace: not applicable for Cardano");
        Err(Error::config(ConfigError::wrong_type()))
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        // Cardano uses "ibc" as commitment prefix
        CommitmentPrefix::try_from(b"ibc".to_vec())
            .map_err(|e| Error::query(format!("invalid commitment prefix for Cardano: {e}")))
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        tracing::debug!("Querying Cardano application status via Gateway");

        // Query latest height from Gateway
        let height = self
            .rt
            .block_on(self.gateway_client.query_latest_height())
            .map_err(|e| {
                tracing::error!("Failed to query latest height: {}", e);
                Error::query(format!("Gateway query_latest_height failed: {}", e))
            })?;

        tracing::info!("Cardano chain at height: {}", height);

        let timestamp = match self.rt.block_on(self.gateway_client.query_header(height)) {
            Ok(header) => header.timestamp,
            Err(e) => {
                tracing::warn!(
                    "Failed to query header at height {height} for timestamp (falling back to local time): {e}"
                );
                tendermint::Time::now().into()
            }
        };

        Ok(ChainStatus { height, timestamp })
    }

    fn query_clients(
        &self,
        _request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        tracing::debug!("Querying all clients");

        // Block on async operation
        self.rt.block_on(async {
            // Query clients from Gateway
            let response_bytes = self.gateway_client
                .query_clients()
                .await
                .map_err(|e| Error::query(format!("Failed to query clients: {}", e)))?;

            // Decode the response
            use prost::Message;
            use ibc_proto::ibc::core::client::v1::QueryClientStatesResponse;

            let response = QueryClientStatesResponse::decode(&response_bytes[..])
                .map_err(|e| Error::query(format!("Failed to decode clients response: {}", e)))?;

            // Convert proto client states to domain types, filtering out unsupported types
            let clients: Vec<IdentifiedAnyClientState> = response
                .client_states
                .into_iter()
                .filter_map(|cs| {
                    IdentifiedAnyClientState::try_from(cs.clone())
                        .map_err(|e| {
                            let (client_type, client_id) = (
                                if let Some(client_state) = &cs.client_state {
                                    client_state.type_url.clone()
                                } else {
                                    "None".to_string()
                                },
                                &cs.client_id
                            );
                            tracing::warn!(
                                "Encountered unsupported client type `{}` while scanning client `{}`, skipping the client",
                                client_type, client_id
                            );
                            tracing::debug!("Failed to parse client state. Error: {}", e);
                        })
                        .ok()
                })
                .collect();

            Ok(clients)
        })
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        tracing::debug!("Querying client state for: {}", request.client_id);

        let response = self
            .rt
            .block_on(
                self.gateway_client
                    .query_client_state(request.client_id.as_str()),
            )
            .map_err(|e| {
                tracing::error!("Failed to query client state: {}", e);
                Error::query(format!("Gateway query_client_state failed: {}", e))
            })?;

        let client_state_any = response
            .client_state
            .ok_or_else(|| Error::query("No client_state in response".to_string()))?;

        let any_client_state: AnyClientState = AnyClientState::try_from(client_state_any.clone())
            .map_err(|e| {
            Error::query(format!(
                "Failed to decode client state {}: {e}",
                client_state_any.type_url
            ))
        })?;

        let proof = if include_proof == IncludeProof::Yes && !response.proof.is_empty() {
            use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
            use prost::Message;

            let raw_proof = RawMerkleProof::decode(&response.proof[..])
                .map_err(|e| Error::query(format!("Failed to decode proof: {e}")))?;
            Some(MerkleProof::from(raw_proof))
        } else {
            None
        };

        Ok((any_client_state, proof))
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        tracing::debug!(
            "Querying consensus state for client: {} at height: {:?}",
            request.client_id,
            request.consensus_height
        );

        let response = self
            .rt
            .block_on(
                self.gateway_client
                    .query_consensus_state(request.client_id.as_str(), request.consensus_height),
            )
            .map_err(|e| {
                tracing::error!("Failed to query consensus state: {}", e);
                Error::query(format!("Gateway query_consensus_state failed: {}", e))
            })?;

        let consensus_state_any = response
            .consensus_state
            .ok_or_else(|| Error::query("No consensus_state in response".to_string()))?;

        let any_consensus_state: AnyConsensusState =
            AnyConsensusState::try_from(consensus_state_any.clone()).map_err(|e| {
                Error::query(format!(
                    "Failed to decode consensus state {}: {e}",
                    consensus_state_any.type_url
                ))
            })?;

        let proof = if include_proof == IncludeProof::Yes && !response.proof.is_empty() {
            use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
            use prost::Message;

            let raw_proof = RawMerkleProof::decode(&response.proof[..])
                .map_err(|e| Error::query(format!("Failed to decode proof: {e}")))?;
            Some(MerkleProof::from(raw_proof))
        } else {
            None
        };

        Ok((any_consensus_state, proof))
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<ICSHeight>, Error> {
        tracing::debug!(
            "Querying consensus state heights for client: {}",
            request.client_id
        );

        self.rt.block_on(async {
            let grpc_request: ibc_proto::ibc::core::client::v1::QueryConsensusStateHeightsRequest =
                request.clone().into();

            let heights_response = self
                .gateway_client
                .query_consensus_state_heights(grpc_request)
                .await;

            let consensus_state_heights = match heights_response {
                Ok(res) => res.consensus_state_heights,
                Err(heights_err) => {
                    // Some chains do not implement `ConsensusStateHeights`; fall back to
                    // `ConsensusStates` and extract the heights.
                    let states_request: ibc_proto::ibc::core::client::v1::QueryConsensusStatesRequest =
                        ibc_proto::ibc::core::client::v1::QueryConsensusStatesRequest {
                            client_id: request.client_id.to_string(),
                            pagination: request.pagination.map(|p| p.into()),
                        };

                    let states = self
                        .gateway_client
                        .query_consensus_states(states_request)
                        .await
                        .map_err(|states_err| {
                            Error::query(format!(
                                "Failed to query consensus state heights ({heights_err}) and fallback consensus states ({states_err})"
                            ))
                        })?;

                    states
                        .consensus_states
                        .into_iter()
                        .filter_map(|cs| cs.height)
                        .collect()
                }
            };

            let mut heights: Vec<_> = consensus_state_heights
                .into_iter()
                .filter_map(|h| {
                    ICSHeight::new(h.revision_number, h.revision_height)
                        .map_err(|e| {
                            tracing::warn!(
                                "Failed to parse consensus state height {}-{}: {}",
                                h.revision_number,
                                h.revision_height,
                                e
                            );
                        })
                        .ok()
                })
                .collect();

            heights.sort_unstable();

            Ok(heights)
        })
    }

    fn query_upgraded_client_state(
        &self,
        _request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        Err(Error::query(
            "Cardano upgraded client state query is not implemented".to_string(),
        ))
    }

    fn query_upgraded_consensus_state(
        &self,
        _request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        Err(Error::query(
            "Cardano upgraded consensus state query is not implemented".to_string(),
        ))
    }

    fn query_connections(
        &self,
        _request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        tracing::debug!("Querying all connections");

        // Block on async operation
        self.rt.block_on(async {
            // Query connections from Gateway
            let response_bytes = self
                .gateway_client
                .query_connections()
                .await
                .map_err(|e| Error::query(format!("Failed to query connections: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::connection::v1::QueryConnectionsResponse;
            use prost::Message;

            let response = QueryConnectionsResponse::decode(&response_bytes[..]).map_err(|e| {
                Error::query(format!("Failed to decode connections response: {}", e))
            })?;

            // Convert proto connections to domain types, filtering out parsing errors
            let connections: Vec<IdentifiedConnectionEnd> = response
                .connections
                .into_iter()
                .filter_map(|co| {
                    IdentifiedConnectionEnd::try_from(co.clone())
                        .map_err(|e| {
                            tracing::warn!(
                                "Connection with ID {} failed parsing. Error: {}",
                                co.id,
                                e
                            );
                        })
                        .ok()
                })
                .collect();

            Ok(connections)
        })
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        tracing::debug!("Querying connections for client: {}", request.client_id);

        // Block on async operation
        self.rt.block_on(async {
            // Query client connections from Gateway
            let response_bytes = self
                .gateway_client
                .query_client_connections(&request.client_id.to_string())
                .await
                .map_err(|e| {
                    // If not found, return empty list
                    if e.to_string().contains("NotFound") {
                        return Error::query("Client connections not found".to_string());
                    }
                    Error::query(format!("Failed to query client connections: {}", e))
                })?;

            // Decode the response
            use ibc_proto::ibc::core::connection::v1::QueryClientConnectionsResponse;
            use prost::Message;
            use std::str::FromStr;

            let response =
                QueryClientConnectionsResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode client connections response: {}",
                        e
                    ))
                })?;

            // Parse connection_paths strings into ConnectionId instances
            let connection_ids: Vec<ConnectionId> = response
                .connection_paths
                .iter()
                .filter_map(|id| {
                    ConnectionId::from_str(id)
                        .map_err(|e| {
                            tracing::warn!(
                                "Connection with ID {} failed parsing. Error: {}",
                                id,
                                e
                            );
                        })
                        .ok()
                })
                .collect();

            Ok(connection_ids)
        })
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        tracing::info!("Querying connection: {:?}", request.connection_id);

        // Block on async operation
        self.rt.block_on(async {
            // Query connection from Gateway
            let response_bytes = self
                .gateway_client
                .query_connection(&request.connection_id.to_string())
                .await
                .map_err(|e| Error::query(format!("Failed to query connection: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::connection::v1::QueryConnectionResponse;
            use prost::Message;

            let response = QueryConnectionResponse::decode(&response_bytes[..]).map_err(|e| {
                Error::query(format!("Failed to decode connection response: {}", e))
            })?;

            let connection_end = response
                .connection
                .ok_or_else(|| Error::query("No connection in response".to_string()))?;

            // Convert proto ConnectionEnd to domain ConnectionEnd
            let connection = ConnectionEnd::try_from(connection_end)
                .map_err(|e| Error::query(format!("Failed to parse ConnectionEnd: {}", e)))?;

            // Parse proof if requested
            let proof = if matches!(include_proof, IncludeProof::Yes) {
                if !response.proof.is_empty() {
                    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
                    let raw_proof = RawMerkleProof::decode(&response.proof[..])
                        .map_err(|e| Error::query(format!("Failed to decode proof: {}", e)))?;
                    Some(MerkleProof::from(raw_proof))
                } else {
                    None
                }
            } else {
                None
            };

            Ok((connection, proof))
        })
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        tracing::debug!(
            "Querying channels for connection: {}",
            request.connection_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query connection channels from Gateway
            let response_bytes = self
                .gateway_client
                .query_connection_channels(&request.connection_id.to_string())
                .await
                .map_err(|e| Error::query(format!("Failed to query connection channels: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryConnectionChannelsResponse;
            use prost::Message;

            let response =
                QueryConnectionChannelsResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode connection channels response: {}",
                        e
                    ))
                })?;

            // Convert proto channels to domain types, filtering out parsing errors
            let channels: Vec<IdentifiedChannelEnd> = response
                .channels
                .into_iter()
                .filter_map(|ch| {
                    IdentifiedChannelEnd::try_from(ch.clone())
                        .map_err(|e| {
                            tracing::warn!(
                                "Channel with port {} and ID {} failed parsing. Error: {}",
                                ch.port_id,
                                ch.channel_id,
                                e
                            );
                        })
                        .ok()
                })
                .collect();

            Ok(channels)
        })
    }

    fn query_channels(
        &self,
        _request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        tracing::debug!("Querying all channels");

        // Block on async operation
        self.rt.block_on(async {
            // Query channels from Gateway
            let response_bytes = self
                .gateway_client
                .query_channels()
                .await
                .map_err(|e| Error::query(format!("Failed to query channels: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryChannelsResponse;
            use prost::Message;

            let response = QueryChannelsResponse::decode(&response_bytes[..])
                .map_err(|e| Error::query(format!("Failed to decode channels response: {}", e)))?;

            // Convert proto channels to domain types, filtering out parsing errors
            let channels: Vec<IdentifiedChannelEnd> = response
                .channels
                .into_iter()
                .filter_map(|ch| {
                    IdentifiedChannelEnd::try_from(ch.clone())
                        .map_err(|e| {
                            tracing::warn!(
                                "Channel with port {} and ID {} failed parsing. Error: {}",
                                ch.port_id,
                                ch.channel_id,
                                e
                            );
                        })
                        .ok()
                })
                .collect();

            Ok(channels)
        })
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        tracing::info!(
            "Querying channel: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query channel from Gateway
            let response_bytes = self
                .gateway_client
                .query_channel(request.port_id.as_ref(), request.channel_id.as_ref())
                .await
                .map_err(|e| Error::query(format!("Failed to query channel: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryChannelResponse;
            use prost::Message;

            let response = QueryChannelResponse::decode(&response_bytes[..])
                .map_err(|e| Error::query(format!("Failed to decode channel response: {}", e)))?;

            let channel_proto = response
                .channel
                .ok_or_else(|| Error::query("No channel in response".to_string()))?;

            // Convert proto Channel to domain ChannelEnd
            let channel = ChannelEnd::try_from(channel_proto)
                .map_err(|e| Error::query(format!("Failed to parse ChannelEnd: {}", e)))?;

            // Parse proof if requested
            let proof = if matches!(include_proof, IncludeProof::Yes) {
                if !response.proof.is_empty() {
                    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
                    let raw_proof = RawMerkleProof::decode(&response.proof[..])
                        .map_err(|e| Error::query(format!("Failed to decode proof: {}", e)))?;
                    Some(MerkleProof::from(raw_proof))
                } else {
                    None
                }
            } else {
                None
            };

            Ok((channel, proof))
        })
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        tracing::debug!(
            "Querying channel client state: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        self.rt.block_on(async {
            let response_bytes = self
                .gateway_client
                .query_channel_client_state(request.port_id.as_ref(), request.channel_id.as_ref())
                .await
                .map_err(|e| Error::query(format!("Failed to query channel client state: {e}")))?;

            use ibc_proto::ibc::core::channel::v1::QueryChannelClientStateResponse;
            use prost::Message;

            let response =
                QueryChannelClientStateResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode channel client state response: {e}"
                    ))
                })?;

            let identified = response
                .identified_client_state
                .and_then(|ics| IdentifiedAnyClientState::try_from(ics).ok());

            Ok(identified)
        })
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        tracing::info!(
            "Querying packet commitment: port={}, channel={}, sequence={}",
            request.port_id,
            request.channel_id,
            request.sequence
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query packet commitment from Gateway
            let response_bytes = self
                .gateway_client
                .query_packet_commitment(
                    request.port_id.as_ref(),
                    request.channel_id.as_ref(),
                    request.sequence.into(),
                )
                .await
                .map_err(|e| Error::query(format!("Failed to query packet commitment: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryPacketCommitmentResponse;
            use prost::Message;

            let response =
                QueryPacketCommitmentResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode packet commitment response: {}",
                        e
                    ))
                })?;

            // Parse proof if requested
            let proof = if matches!(include_proof, IncludeProof::Yes) {
                if !response.proof.is_empty() {
                    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
                    let raw_proof = RawMerkleProof::decode(&response.proof[..])
                        .map_err(|e| Error::query(format!("Failed to decode proof: {}", e)))?;
                    Some(MerkleProof::from(raw_proof))
                } else {
                    None
                }
            } else {
                None
            };

            Ok((response.commitment, proof))
        })
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        tracing::info!(
            "Querying packet commitments: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query packet commitments from Gateway
            let response_bytes = self
                .gateway_client
                .query_packet_commitments(request.port_id.as_ref(), request.channel_id.as_ref())
                .await
                .map_err(|e| Error::query(format!("Failed to query packet commitments: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryPacketCommitmentsResponse;
            use prost::Message;

            let response =
                QueryPacketCommitmentsResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode packet commitments response: {}",
                        e
                    ))
                })?;

            // Extract sequences from packet_states
            let sequences: Vec<Sequence> = response
                .commitments
                .iter()
                .map(|state| Sequence::from(state.sequence))
                .collect();

            // Extract height from response
            let height = response.height.ok_or_else(|| {
                Error::query("No height in packet commitments response".to_string())
            })?;

            let ics_height = ICSHeight::new(height.revision_number, height.revision_height)
                .map_err(|e| Error::query(format!("Invalid height: {}", e)))?;

            Ok((sequences, ics_height))
        })
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        tracing::info!(
            "Querying packet receipt: port={}, channel={}, sequence={}",
            request.port_id,
            request.channel_id,
            request.sequence
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query packet receipt from Gateway
            let response_bytes = self
                .gateway_client
                .query_packet_receipt(
                    request.port_id.as_ref(),
                    request.channel_id.as_ref(),
                    request.sequence.into(),
                )
                .await
                .map_err(|e| Error::query(format!("Failed to query packet receipt: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryPacketReceiptResponse;
            use prost::Message;

            let response =
                QueryPacketReceiptResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!("Failed to decode packet receipt response: {}", e))
                })?;

            // The receipt is a boolean - convert to bytes
            let receipt_bytes = if response.received {
                vec![1u8]
            } else {
                vec![0u8]
            };

            // Parse proof if requested
            let proof = if matches!(include_proof, IncludeProof::Yes) {
                if !response.proof.is_empty() {
                    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
                    let raw_proof = RawMerkleProof::decode(&response.proof[..])
                        .map_err(|e| Error::query(format!("Failed to decode proof: {}", e)))?;
                    Some(MerkleProof::from(raw_proof))
                } else {
                    None
                }
            } else {
                None
            };

            Ok((receipt_bytes, proof))
        })
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        tracing::info!(
            "Querying unreceived packets: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query unreceived packets from Gateway
            let response_bytes = self
                .gateway_client
                .query_unreceived_packets(
                    request.port_id.as_ref(),
                    request.channel_id.as_ref(),
                    request
                        .packet_commitment_sequences
                        .iter()
                        .map(|s| (*s).into())
                        .collect(),
                )
                .await
                .map_err(|e| Error::query(format!("Failed to query unreceived packets: {}", e)))?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryUnreceivedPacketsResponse;
            use prost::Message;

            let response =
                QueryUnreceivedPacketsResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode unreceived packets response: {}",
                        e
                    ))
                })?;

            // Extract sequences from response
            let sequences: Vec<Sequence> = response
                .sequences
                .iter()
                .map(|s| Sequence::from(*s))
                .collect();

            Ok(sequences)
        })
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        tracing::info!(
            "Querying packet acknowledgement: port={}, channel={}, sequence={}",
            request.port_id,
            request.channel_id,
            request.sequence
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query packet acknowledgement from Gateway
            let response_bytes = self
                .gateway_client
                .query_packet_acknowledgement(
                    request.port_id.as_ref(),
                    request.channel_id.as_ref(),
                    request.sequence.into(),
                )
                .await
                .map_err(|e| {
                    Error::query(format!("Failed to query packet acknowledgement: {}", e))
                })?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryPacketAcknowledgementResponse;
            use prost::Message;

            let response = QueryPacketAcknowledgementResponse::decode(&response_bytes[..])
                .map_err(|e| {
                    Error::query(format!(
                        "Failed to decode packet acknowledgement response: {}",
                        e
                    ))
                })?;

            // Parse proof if requested
            let proof = if matches!(include_proof, IncludeProof::Yes) {
                if !response.proof.is_empty() {
                    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
                    let raw_proof = RawMerkleProof::decode(&response.proof[..])
                        .map_err(|e| Error::query(format!("Failed to decode proof: {}", e)))?;
                    Some(MerkleProof::from(raw_proof))
                } else {
                    None
                }
            } else {
                None
            };

            Ok((response.acknowledgement, proof))
        })
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error> {
        tracing::info!(
            "Querying packet acknowledgements: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query packet acknowledgements from Gateway
            let response_bytes = self
                .gateway_client
                .query_packet_acknowledgements(
                    request.port_id.as_ref(),
                    request.channel_id.as_ref(),
                )
                .await
                .map_err(|e| {
                    Error::query(format!("Failed to query packet acknowledgements: {}", e))
                })?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryPacketAcknowledgementsResponse;
            use prost::Message;

            let response = QueryPacketAcknowledgementsResponse::decode(&response_bytes[..])
                .map_err(|e| {
                    Error::query(format!(
                        "Failed to decode packet acknowledgements response: {}",
                        e
                    ))
                })?;

            // Extract sequences from acknowledgements
            let sequences: Vec<Sequence> = response
                .acknowledgements
                .iter()
                .map(|ack| Sequence::from(ack.sequence))
                .collect();

            // Extract height from response
            let height = response.height.ok_or_else(|| {
                Error::query("No height in packet acknowledgements response".to_string())
            })?;

            let ics_height = ICSHeight::new(height.revision_number, height.revision_height)
                .map_err(|e| Error::query(format!("Invalid height: {}", e)))?;

            Ok((sequences, ics_height))
        })
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        tracing::info!(
            "Querying unreceived acknowledgements: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query unreceived acknowledgements from Gateway
            let response_bytes = self
                .gateway_client
                .query_unreceived_acknowledgements(
                    request.port_id.as_ref(),
                    request.channel_id.as_ref(),
                    request
                        .packet_ack_sequences
                        .iter()
                        .map(|s| (*s).into())
                        .collect(),
                )
                .await
                .map_err(|e| {
                    Error::query(format!(
                        "Failed to query unreceived acknowledgements: {}",
                        e
                    ))
                })?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryUnreceivedAcksResponse;
            use prost::Message;

            let response =
                QueryUnreceivedAcksResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!("Failed to decode unreceived acks response: {}", e))
                })?;

            // Extract sequences from response
            let sequences: Vec<Sequence> = response
                .sequences
                .iter()
                .map(|s| Sequence::from(*s))
                .collect();

            Ok(sequences)
        })
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        tracing::info!(
            "Querying next sequence receive: port={}, channel={}",
            request.port_id,
            request.channel_id
        );

        // Block on async operation
        self.rt.block_on(async {
            // Query next sequence receive from Gateway
            let response_bytes = self
                .gateway_client
                .query_next_sequence_receive(request.port_id.as_ref(), request.channel_id.as_ref())
                .await
                .map_err(|e| {
                    Error::query(format!("Failed to query next sequence receive: {}", e))
                })?;

            // Decode the response
            use ibc_proto::ibc::core::channel::v1::QueryNextSequenceReceiveResponse;
            use prost::Message;

            let response =
                QueryNextSequenceReceiveResponse::decode(&response_bytes[..]).map_err(|e| {
                    Error::query(format!(
                        "Failed to decode next sequence receive response: {}",
                        e
                    ))
                })?;

            let sequence = Sequence::from(response.next_sequence_receive);

            // Parse proof if requested
            let proof = if matches!(include_proof, IncludeProof::Yes) {
                if !response.proof.is_empty() {
                    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
                    let raw_proof = RawMerkleProof::decode(&response.proof[..])
                        .map_err(|e| Error::query(format!("Failed to decode proof: {}", e)))?;
                    Some(MerkleProof::from(raw_proof))
                } else {
                    None
                }
            } else {
                None
            };

            Ok((sequence, proof))
        })
    }

    fn query_txs(&self, _request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        use crate::chain::requests::{QueryHeight, QueryTxRequest};
        use ibc_relayer_types::events::WithBlockDataType;

        match _request {
            QueryTxRequest::Transaction(tx) => {
                self.rt.block_on(async {
                    let response = self
                        .gateway_client
                        .query_transaction_by_hash(tx.0.to_string())
                        .await
                        .map_err(|e| Error::query(format!("Failed to query transaction by hash: {e}")))?;

                    let height = ICSHeight::new(0, response.height)
                        .map_err(|e| Error::query(format!("Invalid tx height {}: {e}", response.height)))?;

                    let proto_events: Vec<super::generated::ibc::cardano::v1::Event> = response
                        .events
                        .into_iter()
                        .map(|e| super::generated::ibc::cardano::v1::Event {
                            r#type: e.r#type,
                            attributes: e
                                .event_attribute
                                .into_iter()
                                .map(|a| super::generated::ibc::cardano::v1::EventAttribute {
                                    key: a.key,
                                    value: a.value,
                                })
                                .collect(),
                        })
                        .collect();

                    let parsed_events = super::event_parser::parse_events(proto_events, height)
                        .map_err(|e| Error::query(format!("Failed to parse tx events: {e}")))?;

                    Ok(parsed_events
                        .into_iter()
                        .map(|ev| IbcEventWithHeight::new(ev, height))
                        .collect())
                })
            }

            QueryTxRequest::Client(request) => {
                self.rt.block_on(async {
                    const LOOKBACK_WINDOW: u64 = 50;

                    let filter_events = |height: ICSHeight,
                                         proto_events: Vec<super::generated::ibc::cardano::v1::Event>|
                     -> Result<Vec<IbcEventWithHeight>, Error> {
                        let parsed_events = super::event_parser::parse_events(proto_events, height)
                            .map_err(|e| Error::query(format!("Failed to parse tx events: {e}")))?;

                        Ok(parsed_events
                            .into_iter()
                            .filter(|ev| match (&request.event_id, ev) {
                                (
                                    WithBlockDataType::CreateClient,
                                    ibc_relayer_types::events::IbcEvent::CreateClient(e),
                                ) => e.client_id() == &request.client_id
                                    && e.0.consensus_height == request.consensus_height,
                                (
                                    WithBlockDataType::UpdateClient,
                                    ibc_relayer_types::events::IbcEvent::UpdateClient(e),
                                ) => e.common.client_id == request.client_id
                                    && e.common.consensus_height == request.consensus_height,
                                _ => false,
                            })
                            .map(|ev| IbcEventWithHeight::new(ev, height))
                            .collect())
                    };

                    match request.query_height {
                        QueryHeight::Specific(h) => {
                            let target_height_u64 = h.revision_height();

                            let response = self
                                .gateway_client
                                .query_block_results(target_height_u64)
                                .await
                                .map_err(|e| Error::query(format!("Failed to query block results: {e}")))?;

                            let block_results = response
                                .block_results
                                .ok_or_else(|| Error::query("No block_results in response".to_string()))?;

                            let height = match block_results.height {
                                Some(h) => ICSHeight::new(h.revision_number, h.revision_height)
                                    .map_err(|e| {
                                        Error::query(format!("Invalid height in block results: {e}"))
                                    })?,
                                None => ICSHeight::new(0, target_height_u64).map_err(|e| {
                                    Error::query(format!(
                                        "Invalid fallback height {target_height_u64} in block results: {e}"
                                    ))
                                })?,
                            };

                            let proto_events: Vec<super::generated::ibc::cardano::v1::Event> = block_results
                                .txs_results
                                .into_iter()
                                .flat_map(|tx| tx.events)
                                .map(|e| super::generated::ibc::cardano::v1::Event {
                                    r#type: e.r#type,
                                    attributes: e
                                        .event_attribute
                                        .into_iter()
                                        .map(|a| super::generated::ibc::cardano::v1::EventAttribute {
                                            key: a.key,
                                            value: a.value,
                                        })
                                        .collect(),
                                })
                                .collect();

                            filter_events(height, proto_events)
                        }
                        QueryHeight::Latest => {
                            let latest = self
                                .gateway_client
                                .query_latest_height()
                                .await
                                .map_err(|e| Error::query(format!("Failed to query latest height: {e}")))?;

                            let latest_h = latest.revision_height();
                            let since_h = latest_h.saturating_sub(LOOKBACK_WINDOW);
                            let since_h = since_h.max(1);
                            let since_height = ICSHeight::new(0, since_h)
                                .map_err(|e| Error::query(format!("Invalid since height {since_h}: {e}")))?;

                            let response = self
                                .gateway_client
                                .query_events(since_height)
                                .await
                                .map_err(|e| Error::query(format!("Failed to query events: {e}")))?;

                            let mut out = Vec::new();
                            for block in response.events {
                                let height = ICSHeight::new(0, block.height)
                                    .map_err(|e| Error::query(format!("Invalid block height {}: {e}", block.height)))?;

                                let proto_events: Vec<super::generated::ibc::cardano::v1::Event> = block
                                    .events
                                    .into_iter()
                                    .flat_map(|tx| tx.events)
                                    .map(|e| super::generated::ibc::cardano::v1::Event {
                                        r#type: e.r#type,
                                        attributes: e
                                            .event_attribute
                                            .into_iter()
                                            .map(|a| super::generated::ibc::cardano::v1::EventAttribute {
                                                key: a.key,
                                                value: a.value,
                                            })
                                            .collect(),
                                    })
                                    .collect();

                                out.extend(filter_events(height, proto_events)?);
                            }

                            Ok(out)
                        }
                    }
                })
            }
        }
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        use crate::chain::requests::{Qualified, QueryHeight};

        let max_height: Option<u64> = match request.height {
            Qualified::SmallerEqual(QueryHeight::Specific(h)) => Some(h.revision_height()),
            Qualified::Equal(QueryHeight::Specific(h)) => Some(h.revision_height()),
            _ => None,
        };

        let must_equal_height: Option<u64> = match request.height {
            Qualified::Equal(QueryHeight::Specific(h)) => Some(h.revision_height()),
            _ => None,
        };

        self.rt.block_on(async {
            let mut out = Vec::new();

            // If the request targets a single height, avoid block search and inspect that block only.
            if let Some(h) = must_equal_height {
                let response = self
                    .gateway_client
                    .query_block_results(h)
                    .await
                    .map_err(|e| Error::query(format!("Failed to query block results: {e}")))?;

                out.extend(filter_packet_events_from_block_results(
                    &request,
                    response.block_results,
                    h,
                )?);
                return Ok(out);
            }

            for seq in &request.sequences {
                let search = self
                    .gateway_client
                    .query_block_search_all(
                        request.source_channel_id.to_string(),
                        request.destination_channel_id.to_string(),
                        seq.to_string(),
                        50,
                    )
                    .await
                    .map_err(|e| Error::query(format!("Failed to search blocks: {e}")))?;

                let mut heights: Vec<u64> = search
                    .blocks
                    .into_iter()
                    .filter_map(|b| b.block.map(|bi| bi.height))
                    .filter_map(|h| u64::try_from(h).ok())
                    .collect();

                heights.sort_unstable();
                heights.dedup();

                if let Some(max_h) = max_height {
                    heights.retain(|h| *h <= max_h);
                }

                for h in heights {
                    let response = self
                        .gateway_client
                        .query_block_results(h)
                        .await
                        .map_err(|e| Error::query(format!("Failed to query block results: {e}")))?;

                    out.extend(filter_packet_events_from_block_results(
                        &request,
                        response.block_results,
                        h,
                    )?);
                }
            }

            Ok(out)
        })
    }

    fn query_host_consensus_state(
        &self,
        _request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        Err(Error::query(
            "Cardano host consensus state query is not implemented".to_string(),
        ))
    }

    fn build_client_state(
        &self,
        height: ICSHeight,
        _settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        tracing::info!(
            "Building Mithril client state for Cardano at height {:?}",
            height
        );

        let response = self
            .rt
            .block_on(
                self.gateway_client
                    .query_new_client(height.revision_height()),
            )
            .map_err(|e| Error::query(format!("Gateway query_new_client failed: {e}")))?;

        let raw_any = response
            .client_state
            .ok_or_else(|| Error::query("No client_state in NewClient response".to_string()))?;

        let any = ibc_proto::google::protobuf::Any {
            type_url: raw_any.type_url,
            value: raw_any.value,
        };

        any.try_into()
            .map_err(|e: ibc_relayer_types::core::ics02_client::error::Error| {
                Error::query(format!("Failed to decode Mithril client state: {e}"))
            })
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        let ibc_state_root = extract_ibc_state_root_from_host_state_tx(
            &light_block.header,
            &light_block.host_state_nft_policy_id,
            &light_block.host_state_nft_token_name,
        )?;

        let header = light_block.header;

        Ok(MithrilConsensusState::new(
            CommitmentRoot::from_bytes(&ibc_state_root),
            header.timestamp.nanoseconds(),
            header.mithril_stake_distribution_certificate,
            header.transaction_snapshot_certificate.hash,
        ))
    }

    fn build_header(
        &mut self,
        _trusted_height: ICSHeight,
        target_height: ICSHeight,
        _client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        // NOTE: Hermes core logic often requests a client update at `proofs_height + 1`.
        //
        // On Tendermint chains this is fine because heights are contiguous and the Tendermint
        // header builder can return intermediate "support" headers (including the proof height).
        //
        // For Cardano/Mithril, however, headers only exist at Mithril-certified transaction snapshot
        // heights (e.g. every ~15 blocks in our devnet setup). That means a height like `H + 1`
        // may not exist at all even if the chain has advanced well beyond it.
        //
        // If the exact `target_height` is not available, we still want to:
        // - install a consensus state at `target_height - 1` (the proof height), so proofs verify, and
        // - also advance the client to the latest available snapshot height.
        //
        // We do this by returning:
        // - `support` header at `target_height - 1`, and
        // - a final header at the latest snapshot height.
        match self
            .rt
            .block_on(self.gateway_client.query_header(target_height))
        {
            Ok(header) => Ok((header, vec![])),
            Err(e) => {
                let err_str = e.to_string();
                if !err_str.contains("Not found") || !err_str.contains("height") {
                    return Err(Error::query(format!("Gateway query_header failed: {e}")));
                }

                let proof_height = target_height
                    .decrement()
                    .map_err(|_| Error::query(format!("invalid target height {target_height}")))?;

                let proof_header = self
                    .rt
                    .block_on(self.gateway_client.query_header(proof_height))
                    .map_err(|e| {
                        Error::query(format!(
                            "Gateway query_header failed at proof height {proof_height}: {e}"
                        ))
                    })?;

                let latest_height = self
                    .rt
                    .block_on(self.gateway_client.query_latest_height())
                    .map_err(|e| {
                        Error::query(format!("Gateway query_latest_height failed: {e}"))
                    })?;

                let mut selected_header = None;
                let mut candidate_height = target_height.revision_height();
                let latest_revision_height = latest_height.revision_height();

                while candidate_height <= latest_revision_height {
                    let candidate_ics_height =
                        ICSHeight::new(target_height.revision_number(), candidate_height)
                            .map_err(|_| {
                                Error::query(format!(
                                    "invalid candidate height while searching Cardano header: {candidate_height}"
                                ))
                            })?;

                    match self
                        .rt
                        .block_on(self.gateway_client.query_header(candidate_ics_height))
                    {
                        Ok(header) => {
                            selected_header = Some(header);
                            break;
                        }
                        Err(search_error) => {
                            let search_error_text = search_error.to_string();
                            if !search_error_text.contains("Not found")
                                || !search_error_text.contains("height")
                            {
                                return Err(Error::query(format!(
                                    "Gateway query_header failed while searching for a certified height at/after {target_height} (candidate {candidate_ics_height}): {search_error}"
                                )));
                            }
                        }
                    }

                    candidate_height = candidate_height.saturating_add(1);
                }

                let selected_header = if let Some(header) = selected_header {
                    header
                } else {
                    self.rt
                        .block_on(self.gateway_client.query_header(latest_height))
                        .map_err(|e| {
                            Error::query(format!(
                                "Gateway query_header failed at latest height {latest_height}: {e}"
                            ))
                        })?
                };

                Ok((selected_header, vec![proof_header]))
            }
        }
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        _channel_id: &ChannelId,
        _port_id: &PortId,
        _counterparty_payee: &Signer,
    ) -> Result<(), Error> {
        // ICS-29 fee middleware - not implemented for Cardano yet
        tracing::warn!("maybe_register_counterparty_payee: not implemented for Cardano");
        Ok(())
    }

    fn cross_chain_query(
        &self,
        _requests: Vec<CrossChainQueryRequest>,
    ) -> Result<
        Vec<ibc_relayer_types::applications::ics31_icq::response::CrossChainQueryResponse>,
        Error,
    > {
        Err(Error::query(
            "ICS-31 cross-chain queries are not supported for Cardano".to_string(),
        ))
    }

    fn query_incentivized_packet(
        &self,
        _request: ibc_proto::ibc::apps::fee::v1::QueryIncentivizedPacketRequest,
    ) -> Result<ibc_proto::ibc::apps::fee::v1::QueryIncentivizedPacketResponse, Error> {
        Err(Error::query(
            "ICS-29 fee middleware is not supported for Cardano".to_string(),
        ))
    }

    fn query_consumer_chains(
        &self,
    ) -> Result<Vec<ibc_relayer_types::applications::ics28_ccv::msgs::ConsumerChain>, Error> {
        Err(Error::query(
            "ICS-28 CCV (Cross-Chain Validation) is not applicable to Cardano".to_string(),
        ))
    }

    fn query_upgrade(
        &self,
        _request: ibc_proto::ibc::core::channel::v1::QueryUpgradeRequest,
        _height: ibc_relayer_types::Height,
        _include_proof: IncludeProof,
    ) -> Result<
        (
            ibc_relayer_types::core::ics04_channel::upgrade::Upgrade,
            Option<MerkleProof>,
        ),
        Error,
    > {
        Err(Error::query(
            "IBC channel upgrades are not implemented for Cardano".to_string(),
        ))
    }

    fn query_upgrade_error(
        &self,
        _request: ibc_proto::ibc::core::channel::v1::QueryUpgradeErrorRequest,
        _height: ibc_relayer_types::Height,
        _include_proof: IncludeProof,
    ) -> Result<
        (
            ibc_relayer_types::core::ics04_channel::upgrade::ErrorReceipt,
            Option<MerkleProof>,
        ),
        Error,
    > {
        Err(Error::query(
            "IBC channel upgrades are not implemented for Cardano".to_string(),
        ))
    }

    fn query_ccv_consumer_id(
        &self,
        _client_id: ClientId,
    ) -> Result<ibc_relayer_types::applications::ics28_ccv::msgs::ConsumerId, Error> {
        Err(Error::query(
            "ICS-28 CCV (Cross-Chain Validation) is not applicable to Cardano".to_string(),
        ))
    }
}

fn filter_packet_events_from_block_results(
    request: &QueryPacketEventDataRequest,
    block_results: Option<super::generated::ibc::core::types::v1::ResultBlockResults>,
    fallback_height: u64,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    use ibc_relayer_types::events::{IbcEvent as RelayerIbcEvent, WithBlockDataType};

    let block_results = match block_results {
        Some(br) => br,
        None => return Ok(vec![]),
    };

    let height = match block_results.height {
        Some(h) => ICSHeight::new(h.revision_number, h.revision_height)
            .map_err(|e| Error::query(format!("Invalid height in block results: {e}")))?,
        None => ICSHeight::new(0, fallback_height)
            .map_err(|e| Error::query(format!("Invalid fallback height {fallback_height}: {e}")))?,
    };

    let proto_events: Vec<super::generated::ibc::cardano::v1::Event> = block_results
        .txs_results
        .into_iter()
        .flat_map(|tx| tx.events)
        .map(|e| super::generated::ibc::cardano::v1::Event {
            r#type: e.r#type,
            attributes: e
                .event_attribute
                .into_iter()
                .map(|a| super::generated::ibc::cardano::v1::EventAttribute {
                    key: a.key,
                    value: a.value,
                })
                .collect(),
        })
        .collect();

    let parsed_events = super::event_parser::parse_events(proto_events, height)
        .map_err(|e| Error::query(format!("Failed to parse block events: {e}")))?;

    let filtered: Vec<IbcEventWithHeight> = parsed_events
        .into_iter()
        .filter(|ev| match (&request.event_id, ev) {
            (WithBlockDataType::SendPacket, RelayerIbcEvent::SendPacket(e)) => {
                request.sequences.contains(&e.packet.sequence)
                    && e.src_port_id() == &request.source_port_id
                    && e.src_channel_id() == &request.source_channel_id
                    && e.dst_port_id() == &request.destination_port_id
                    && e.dst_channel_id() == &request.destination_channel_id
            }
            (WithBlockDataType::WriteAck, RelayerIbcEvent::WriteAcknowledgement(e)) => {
                request.sequences.contains(&e.packet.sequence)
                    && e.src_port_id() == &request.source_port_id
                    && e.src_channel_id() == &request.source_channel_id
                    && e.dst_port_id() == &request.destination_port_id
                    && e.dst_channel_id() == &request.destination_channel_id
            }
            _ => false,
        })
        .map(|ev| IbcEventWithHeight::new(ev, height))
        .collect();

    Ok(filtered)
}

// Mithril header is decoded from the Gateway as `google.protobuf.Any`.
// See `ibc-relayer-types/src/clients/ics08_cardano/header.rs` and
// `ibc-relayer-types/src/core/ics02_client/header.rs`.

fn extract_ibc_state_root_from_host_state_tx(
    header: &MithrilHeader,
    host_state_nft_policy_id: &[u8],
    host_state_nft_token_name: &[u8],
) -> Result<Vec<u8>, Error> {
    let tx_hash = header.host_state_tx_hash.trim();
    if tx_hash.is_empty() {
        return Err(Error::query(
            "missing host_state_tx_hash in Mithril header".to_string(),
        ));
    }

    if host_state_nft_policy_id.len() != 28 {
        return Err(Error::query(format!(
            "invalid host_state_nft_policy_id length: expected 28 bytes, got {}",
            host_state_nft_policy_id.len()
        )));
    }

    let tx_body_cbor = header.host_state_tx_body_cbor.as_slice();
    if tx_body_cbor.is_empty() {
        return Err(Error::query(
            "missing host_state_tx_body_cbor in Mithril header".to_string(),
        ));
    }

    let computed = blake2b_256(tx_body_cbor);
    let computed_hex = hex::encode(computed);
    if !computed_hex.eq_ignore_ascii_case(tx_hash) {
        return Err(Error::query(format!(
            "HostState tx body hash mismatch: expected {tx_hash}, got {computed_hex}"
        )));
    }

    use pallas_codec::minicbor;
    use pallas_codec::utils::KeepRaw;
    use pallas_primitives::{babbage, conway};

    let conway_body: Result<KeepRaw<'_, conway::MintedTransactionBody<'_>>, _> =
        minicbor::decode(tx_body_cbor);
    if let Ok(body) = conway_body {
        return extract_root_from_conway_tx_body(
            &body,
            header.host_state_tx_output_index,
            host_state_nft_policy_id,
            host_state_nft_token_name,
        );
    }

    let babbage_body: Result<KeepRaw<'_, babbage::MintedTransactionBody<'_>>, _> =
        minicbor::decode(tx_body_cbor);
    if let Ok(body) = babbage_body {
        return extract_root_from_babbage_tx_body(
            &body,
            header.host_state_tx_output_index,
            host_state_nft_policy_id,
            host_state_nft_token_name,
        );
    }

    Err(Error::query(
        "unsupported HostState transaction body CBOR".to_string(),
    ))
}

fn blake2b_256(data: &[u8]) -> [u8; 32] {
    use blake2::digest::consts::U32;
    use blake2::{Blake2b, Digest};

    let mut hasher = Blake2b::<U32>::new();
    hasher.update(data);
    let digest = hasher.finalize();

    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn extract_root_from_conway_tx_body<'a>(
    body: &pallas_codec::utils::KeepRaw<'a, pallas_primitives::conway::MintedTransactionBody<'a>>,
    output_index: u32,
    host_state_nft_policy_id: &[u8],
    host_state_nft_token_name: &[u8],
) -> Result<Vec<u8>, Error> {
    use pallas_primitives::conway::{MintedTransactionOutput, PseudoTransactionOutput};

    let idx: usize = output_index
        .try_into()
        .map_err(|_| Error::query("host_state_tx_output_index out of range".to_string()))?;

    let output: &MintedTransactionOutput<'a> = body
        .outputs
        .get(idx)
        .ok_or_else(|| Error::query("host_state_tx_output_index out of range".to_string()))?;

    let out = match output {
        PseudoTransactionOutput::PostAlonzo(out) => out,
        _ => {
            return Err(Error::query(
                "HostState output is not a post-Alonzo output".to_string(),
            ))
        }
    };

    ensure_value_contains_host_state_nft_conway(
        &out.value,
        host_state_nft_policy_id,
        host_state_nft_token_name,
    )?;

    let datum_option = out.datum_option.as_ref().ok_or_else(|| {
        Error::query("HostState output has no datum option (expected inline datum)".to_string())
    })?;

    let plutus_data = match datum_option {
        pallas_primitives::babbage::PseudoDatumOption::Data(cbor_wrap) => {
            std::ops::Deref::deref(std::ops::Deref::deref(cbor_wrap))
        }
        _ => {
            return Err(Error::query(
                "HostState output does not contain an inline datum".to_string(),
            ))
        }
    };

    extract_ibc_state_root_from_host_state_datum(plutus_data, host_state_nft_policy_id)
}

fn extract_root_from_babbage_tx_body<'a>(
    body: &pallas_codec::utils::KeepRaw<'a, pallas_primitives::babbage::MintedTransactionBody<'a>>,
    output_index: u32,
    host_state_nft_policy_id: &[u8],
    host_state_nft_token_name: &[u8],
) -> Result<Vec<u8>, Error> {
    use pallas_primitives::babbage::{MintedTransactionOutput, PseudoTransactionOutput};

    let idx: usize = output_index
        .try_into()
        .map_err(|_| Error::query("host_state_tx_output_index out of range".to_string()))?;

    let output: &MintedTransactionOutput<'a> = body
        .outputs
        .get(idx)
        .ok_or_else(|| Error::query("host_state_tx_output_index out of range".to_string()))?;

    let out = match output {
        PseudoTransactionOutput::PostAlonzo(out) => out,
        _ => {
            return Err(Error::query(
                "HostState output is not a post-Alonzo output".to_string(),
            ))
        }
    };

    ensure_value_contains_host_state_nft_alonzo(
        &out.value,
        host_state_nft_policy_id,
        host_state_nft_token_name,
    )?;

    let datum_option = out.datum_option.as_ref().ok_or_else(|| {
        Error::query("HostState output has no datum option (expected inline datum)".to_string())
    })?;

    let plutus_data = match datum_option {
        pallas_primitives::babbage::PseudoDatumOption::Data(cbor_wrap) => {
            std::ops::Deref::deref(std::ops::Deref::deref(cbor_wrap))
        }
        _ => {
            return Err(Error::query(
                "HostState output does not contain an inline datum".to_string(),
            ))
        }
    };

    extract_ibc_state_root_from_host_state_datum(plutus_data, host_state_nft_policy_id)
}

fn ensure_value_contains_host_state_nft_conway(
    value: &pallas_primitives::conway::Value,
    host_state_nft_policy_id: &[u8],
    host_state_nft_token_name: &[u8],
) -> Result<(), Error> {
    match value {
        pallas_primitives::conway::Value::Multiasset(_, multiasset) => {
            for (policy, assets) in multiasset.iter() {
                if policy.as_ref() != host_state_nft_policy_id {
                    continue;
                }

                for (asset, amount) in assets.iter() {
                    if asset.as_slice() == host_state_nft_token_name {
                        let amount_u64: u64 = amount.into();
                        if amount_u64 == 1 {
                            return Ok(());
                        }
                    }
                }
            }

            Err(Error::query(
                "HostState output does not contain the expected HostState NFT".to_string(),
            ))
        }
        _ => Err(Error::query(
            "HostState output has no multi-assets (expected HostState NFT)".to_string(),
        )),
    }
}

fn ensure_value_contains_host_state_nft_alonzo(
    value: &pallas_primitives::alonzo::Value,
    host_state_nft_policy_id: &[u8],
    host_state_nft_token_name: &[u8],
) -> Result<(), Error> {
    match value {
        pallas_primitives::alonzo::Value::Multiasset(_, multiasset) => {
            for (policy, assets) in multiasset.iter() {
                if policy.as_ref() != host_state_nft_policy_id {
                    continue;
                }

                for (asset, amount) in assets.iter() {
                    if asset.as_slice() == host_state_nft_token_name && *amount == 1 {
                        return Ok(());
                    }
                }
            }

            Err(Error::query(
                "HostState output does not contain the expected HostState NFT".to_string(),
            ))
        }
        _ => Err(Error::query(
            "HostState output has no multi-assets (expected HostState NFT)".to_string(),
        )),
    }
}

fn extract_ibc_state_root_from_host_state_datum(
    datum: &pallas_primitives::alonzo::PlutusData,
    expected_nft_policy_id: &[u8],
) -> Result<Vec<u8>, Error> {
    use pallas_primitives::alonzo::PlutusData;

    let outer = match datum {
        PlutusData::Constr(c) => c,
        _ => {
            return Err(Error::query(
                "HostState datum is not a constructor PlutusData".to_string(),
            ))
        }
    };

    if plutus_constructor_index(outer) != Some(0) || outer.fields.len() < 2 {
        return Err(Error::query(
            "HostState datum does not match expected constructor shape".to_string(),
        ));
    }

    let state = &outer.fields[0];
    let nft_policy = &outer.fields[1];

    if !expected_nft_policy_id.is_empty() {
        let nft_policy_bytes: &[u8] = match nft_policy {
            PlutusData::BoundedBytes(bytes) => bytes.as_slice(),
            _ => {
                return Err(Error::query(
                    "HostState datum nft_policy is not a byte string".to_string(),
                ))
            }
        };

        if nft_policy_bytes != expected_nft_policy_id {
            return Err(Error::query(
                "unexpected HostState nft_policy in datum".to_string(),
            ));
        }
    }

    let state = match state {
        PlutusData::Constr(c) => c,
        _ => {
            return Err(Error::query(
                "HostState state is not a constructor".to_string(),
            ))
        }
    };

    if plutus_constructor_index(state) != Some(0) || state.fields.len() < 2 {
        return Err(Error::query(
            "HostState state does not match expected constructor shape".to_string(),
        ));
    }

    let root: &[u8] = match &state.fields[1] {
        PlutusData::BoundedBytes(bytes) => bytes.as_slice(),
        _ => {
            return Err(Error::query(
                "ibc_state_root is not a byte string".to_string(),
            ))
        }
    };

    if root.len() != 32 {
        return Err(Error::query(format!(
            "invalid ibc_state_root length: expected 32 bytes, got {}",
            root.len()
        )));
    }

    Ok(root.to_vec())
}

fn plutus_constructor_index(
    constr: &pallas_primitives::alonzo::Constr<pallas_primitives::alonzo::PlutusData>,
) -> Option<u64> {
    match constr.tag {
        102 => constr.any_constructor,
        121..=127 => Some(constr.tag - 121),
        1280..=1400 => Some(constr.tag - 1280 + 7),
        _ => None,
    }
}
