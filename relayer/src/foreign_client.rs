//! Queries and methods for interfacing with foreign clients.
//!
//! The term "foreign client" refers to IBC light clients that are running on-chain,
//! i.e. they are *foreign* to the relayer. In contrast, the term "local client"
//! refers to light clients running *locally* as part of the relayer.

use core::{fmt, time::Duration};
use std::thread;
use std::time::Instant;

use ibc_proto::google::protobuf::Any;
use itertools::Itertools;
use tracing::{debug, error, info, span, trace, warn, Level};

use flex_error::define_error;
use ibc::core::ics02_client::client_consensus::{
    AnyConsensusState, AnyConsensusStateWithHeight, ConsensusState, QueryClientEventRequest,
};
use ibc::core::ics02_client::client_state::AnyClientState;
use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics02_client::error::Error as ClientError;
use ibc::core::ics02_client::events::UpdateClient;
use ibc::core::ics02_client::header::{AnyHeader, Header};
use ibc::core::ics02_client::misbehaviour::MisbehaviourEvidence;
use ibc::core::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::core::ics02_client::msgs::misbehavior::MsgSubmitAnyMisbehaviour;
use ibc::core::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::core::ics02_client::msgs::upgrade_client::MsgUpgradeAnyClient;
use ibc::core::ics02_client::trust_threshold::TrustThreshold;
use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc::downcast;
use ibc::events::{IbcEvent, WithBlockDataType};
use ibc::query::QueryTxRequest;
use ibc::timestamp::{Timestamp, TimestampOverflowError};
use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::client::ClientSettings;
use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    PageRequest, QueryClientStateRequest, QueryConsensusStateRequest, QueryConsensusStatesRequest,
    QueryUpgradedClientStateRequest, QueryUpgradedConsensusStateRequest,
};
use crate::chain::tracking::TrackedMsgs;
use crate::error::Error as RelayerError;

const MAX_MISBEHAVIOUR_CHECK_DURATION: Duration = Duration::from_secs(120);

const MAX_RETRIES: usize = 5;

define_error! {
    ForeignClientError {
        ClientCreate
            {
                chain_id: ChainId,
                description: String
            }
            [ RelayerError ]
            |e| {
                format_args!("error raised while creating client for chain {0}: {1}",
                    e.chain_id, e.description)
            },

        Client
            [ ClientError ]
            |_| { "ICS02 client error" },

        HeaderInTheFuture
            {
                src_chain_id: ChainId,
                src_header_height: Height,
                src_header_time: Timestamp,
                dst_chain_id: ChainId,
                dst_latest_header_height: Height,
                dst_latest_header_time: Timestamp,
                max_drift: Duration
            }
            |e| {
                format_args!("update header from {} with height {} and time {} is in the future compared with latest header on {} with height {} and time {}, adjusted with drift {:?}",
                 e.src_chain_id, e.src_header_height, e.src_header_time, e.dst_chain_id, e.dst_latest_header_height, e.dst_latest_header_time, e.max_drift)
            },

        ClientUpdate
            {
                chain_id: ChainId,
                description: String
            }
            [ RelayerError ]
            |e| {
                format_args!("error raised while updating client on chain {0}: {1}", e.chain_id, e.description)
            },

        ClientUpdateTiming
            {
                chain_id: ChainId,
                clock_drift: Duration,
                description: String
            }
            [ TimestampOverflowError ]
            |e| {
                format_args!("error raised while updating client on chain {0}: {1}", e.chain_id, e.description)
            },

        ClientAlreadyUpToDate
            {
                client_id: ClientId,
                chain_id: ChainId,
                height: Height,
            }
            |e| {
                format_args!("Client {} is already up-to-date with chain {}@{}",
                    e.client_id, e.chain_id, e.height)
            },

        MissingSmallerTrustedHeight
            {
                chain_id: ChainId,
                target_height: Height,
            }
            |e| {
                format_args!("chain {} is missing trusted state smaller than target height {}",
                    e.chain_id, e.target_height)
            },

        MissingTrustedHeight
            {
                chain_id: ChainId,
                target_height: Height,
            }
            |e| {
                format_args!("chain {} is missing trusted state at target height {}",
                    e.chain_id, e.target_height)
            },

        ClientRefresh
            {
                client_id: ClientId,
                reason: String
            }
            [ RelayerError ]
            |e| {
                format_args!("error raised while trying to refresh client {0}: {1}",
                    e.client_id, e.reason)
            },

        ClientQuery
            {
                client_id: ClientId,
                chain_id: ChainId,
            }
            [ RelayerError ]
            |e| {
                format_args!("failed while querying for client {0} on chain id {1}",
                    e.client_id, e.chain_id)
            },

        ClientConsensusQuery
            {
                client_id: ClientId,
                chain_id: ChainId,
                height: Height
            }
            [ RelayerError ]
            |e| {
                format_args!("failed while querying for client consensus state {0} on chain id {1} for height {2}",
                    e.client_id, e.chain_id, e.height)
            },

        ClientUpgrade
            {
                client_id: ClientId,
                chain_id: ChainId,
                description: String,
            }
            [ RelayerError ]
            |e| {
                format_args!("failed while trying to upgrade client id {0} for chain {1}: {2}: {3}",
                    e.client_id, e.chain_id, e.description, e.source)
            },

        ClientEventQuery
            {
                client_id: ClientId,
                chain_id: ChainId,
                consensus_height: Height
            }
            [ RelayerError ]
            |e| {
                format_args!("failed while querying Tx for client {0} on chain id {1} at consensus height {2}",
                    e.client_id, e.chain_id, e.consensus_height)
            },

        UnexpectedEvent
            {
                client_id: ClientId,
                chain_id: ChainId,
                event: String,
            }
            |e| {
                format_args!("failed while querying Tx for client {0} on chain id {1}: query Tx-es returned unexpected event: {2}",
                    e.client_id, e.chain_id, e.event)
            },

        MismatchChainId
            {
                client_id: ClientId,
                expected_chain_id: ChainId,
                actual_chain_id: ChainId,
            }
            |e| {
                format_args!("failed while finding client {0}: expected chain_id in client state: {1}; actual chain_id: {2}",
                    e.client_id, e.expected_chain_id, e.actual_chain_id)
            },

        ExpiredOrFrozen
            {
                client_id: ClientId,
                chain_id: ChainId,
                description: String,
            }
            |e| {
                format_args!("client {0} on chain id {1} is expired or frozen: {2}",
                    e.client_id, e.chain_id, e.description)
            },

        ConsensusStateNotTrusted
            {
                height: Height,
                elapsed: Duration,
            }
            |e| {
                format_args!("the consensus state at height {} is outside of trusting period: elapsed {:?}",
                    e.height, e.elapsed)
            },

        Misbehaviour
            {
                description: String,
            }
            [ RelayerError ]
            |e| {
                format_args!("error raised while checking for misbehaviour evidence: {0}", e.description)
            },

        MisbehaviourExit
            { reason: String }
            |e| {
                format_args!("cannot run misbehaviour: {0}", e.reason)
            },

        SameChainId
            {
                chain_id: ChainId
            }
            |e| {
                format_args!("the chain ID ({}) at the source and destination chains must be different", e.chain_id)
            },

        MissingClientIdFromEvent
            { event: IbcEvent }
            |e| {
                format_args!("cannot extract client_id from result: {:?}",
                    e.event)
            },

        ChainErrorEvent
            {
                chain_id: ChainId,
                event: IbcEvent
            }
            |e| {
                format_args!("failed to update client on destination {} because of error event: {}",
                    e.chain_id, e.event)
            },
    }
}

pub trait HasExpiredOrFrozenError {
    fn is_expired_or_frozen_error(&self) -> bool;
}

impl HasExpiredOrFrozenError for ForeignClientErrorDetail {
    fn is_expired_or_frozen_error(&self) -> bool {
        matches!(self, Self::ExpiredOrFrozen(_))
    }
}

impl HasExpiredOrFrozenError for ForeignClientError {
    fn is_expired_or_frozen_error(&self) -> bool {
        self.detail().is_expired_or_frozen_error()
    }
}

/// User-supplied options for the [`ForeignClient::build_create_client`] operation.
///
/// Currently, the parameters are specific to the Tendermint-based chains.
/// A future revision will bring differentiated options for other chain types.
#[derive(Debug, Default)]
pub struct CreateOptions {
    pub max_clock_drift: Option<Duration>,
    pub trusting_period: Option<Duration>,
    pub trust_threshold: Option<TrustThreshold>,
}

/// Captures the diagnostic of verifying whether a certain
/// consensus state is within the trusting period (i.e., trusted)
/// or it's not within the trusting period (not trusted).
pub enum ConsensusStateTrusted {
    NotTrusted {
        elapsed: Duration,
        network_timestamp: Timestamp,
        consensus_state_timestmap: Timestamp,
    },
    Trusted {
        elapsed: Duration,
    },
}

#[derive(Clone, Debug)]
pub struct ForeignClient<DstChain: ChainHandle, SrcChain: ChainHandle> {
    /// The identifier of this client. The host chain determines this id upon client creation,
    /// so we may be using the default value temporarily.
    pub id: ClientId,

    /// A handle to the chain hosting this client, i.e., destination chain.
    pub dst_chain: DstChain,

    /// A handle to the chain whose headers this client is verifying, aka the source chain.
    pub src_chain: SrcChain,
}

/// Used in Output messages.
/// Provides a concise description of a [`ForeignClient`],
/// using the format:
///     {CHAIN-ID} -> {CHAIN-ID}:{CLIENT}
/// where the first chain identifier is for the source
/// chain, and the second chain identifier is the
/// destination (which hosts the client) chain.
impl<DstChain: ChainHandle, SrcChain: ChainHandle> fmt::Display
    for ForeignClient<DstChain, SrcChain>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} -> {}:{}",
            self.src_chain.id(),
            self.dst_chain.id(),
            self.id
        )
    }
}

impl<DstChain: ChainHandle, SrcChain: ChainHandle> ForeignClient<DstChain, SrcChain> {
    /// Creates a new foreign client on `dst_chain`. Blocks until the client is created, or
    /// an error occurs.
    /// Post-condition: `dst_chain` hosts an IBC client for `src_chain`.
    pub fn new(
        dst_chain: DstChain,
        src_chain: SrcChain,
    ) -> Result<ForeignClient<DstChain, SrcChain>, ForeignClientError> {
        // Sanity check
        if src_chain.id().eq(&dst_chain.id()) {
            return Err(ForeignClientError::same_chain_id(src_chain.id()));
        }

        let mut client = ForeignClient {
            id: ClientId::default(),
            dst_chain,
            src_chain,
        };

        client.create()?;

        Ok(client)
    }

    pub fn restore(
        id: ClientId,
        dst_chain: DstChain,
        src_chain: SrcChain,
    ) -> ForeignClient<DstChain, SrcChain> {
        ForeignClient {
            id,
            dst_chain,
            src_chain,
        }
    }

    /// Queries `host_chain` to verify that a client with identifier `client_id` exists.
    /// If the client does not exist, returns an error. If the client exists, cross-checks that the
    /// identifier for the target chain of this client (i.e., the chain whose headers this client is
    /// verifying) is consistent with `expected_target_chain`, and if so, return a new
    /// `ForeignClient` representing this client.
    pub fn find(
        expected_target_chain: SrcChain,
        host_chain: DstChain,
        client_id: &ClientId,
    ) -> Result<ForeignClient<DstChain, SrcChain>, ForeignClientError> {
        let height = Height::new(expected_target_chain.id().version(), 0);

        match host_chain.query_client_state(QueryClientStateRequest {
            client_id: client_id.clone(),
            height,
        }) {
            Ok(cs) => {
                if cs.chain_id() != expected_target_chain.id() {
                    Err(ForeignClientError::mismatch_chain_id(
                        client_id.clone(),
                        expected_target_chain.id(),
                        cs.chain_id(),
                    ))
                } else {
                    // TODO: Any additional checks?
                    Ok(ForeignClient::restore(
                        client_id.clone(),
                        host_chain,
                        expected_target_chain,
                    ))
                }
            }
            Err(e) => Err(ForeignClientError::client_query(
                client_id.clone(),
                host_chain.id(),
                e,
            )),
        }
    }

    pub fn upgrade(&self) -> Result<Vec<IbcEvent>, ForeignClientError> {
        // Fetch the latest height of the source chain.
        let src_height = self.src_chain.query_latest_height().map_err(|e| {
            ForeignClientError::client_upgrade(
                self.id.clone(),
                self.src_chain.id(),
                "failed while querying src chain for latest height".to_string(),
                e,
            )
        })?;

        info!("[{}] upgrade Height: {}", self, src_height);

        let mut msgs = self.build_update_client(src_height)?;

        // Query the host chain for the upgraded client state, consensus state & their proofs.
        let (client_state, proof_upgrade_client) = self
            .src_chain
            .query_upgraded_client_state(QueryUpgradedClientStateRequest { height: src_height })
            .map_err(|e| {
                ForeignClientError::client_upgrade(
                    self.id.clone(),
                    self.src_chain.id(),
                    "failed while fetching from chain the upgraded client state".to_string(),
                    e,
                )
            })?;

        debug!("[{}] upgraded client state {:?}", self, client_state);

        let (consensus_state, proof_upgrade_consensus_state) = self
            .src_chain
            .query_upgraded_consensus_state(QueryUpgradedConsensusStateRequest {
                height: src_height,
            })
            .map_err(|e| {
                ForeignClientError::client_upgrade(
                    self.id.clone(),
                    self.src_chain.id(),
                    "failed while fetching from chain the upgraded client consensus state"
                        .to_string(),
                    e,
                )
            })?;

        debug!(
            "[{}]  upgraded client consensus state {:?}",
            self, consensus_state
        );

        // Get signer
        let signer = self.dst_chain.get_signer().map_err(|e| {
            ForeignClientError::client_upgrade(
                self.id.clone(),
                self.dst_chain.id(),
                "failed while fetching the destination chain signer".to_string(),
                e,
            )
        })?;

        let msg_upgrade = MsgUpgradeAnyClient {
            client_id: self.id.clone(),
            client_state,
            consensus_state,
            proof_upgrade_client: proof_upgrade_client.into(),
            proof_upgrade_consensus_state: proof_upgrade_consensus_state.into(),
            signer,
        }
        .to_any();

        msgs.push(msg_upgrade);

        let tm = TrackedMsgs::new_static(msgs, "upgrade client");

        let res = self
            .dst_chain
            .send_messages_and_wait_commit(tm)
            .map_err(|e| {
                ForeignClientError::client_upgrade(
                    self.id.clone(),
                    self.dst_chain.id(),
                    "failed while sending message to destination chain".to_string(),
                    e,
                )
            })?;

        Ok(res)
    }

    /// Returns a handle to the chain hosting this client.
    pub fn dst_chain(&self) -> DstChain {
        self.dst_chain.clone()
    }

    /// Returns a handle to the chain whose headers this client is sourcing (the source chain).
    pub fn src_chain(&self) -> SrcChain {
        self.src_chain.clone()
    }

    pub fn id(&self) -> &ClientId {
        &self.id
    }

    /// Lower-level interface for preparing a message to create a client.
    pub fn build_create_client(
        &self,
        options: CreateOptions,
    ) -> Result<MsgCreateAnyClient, ForeignClientError> {
        // Get signer
        let signer = self.dst_chain.get_signer().map_err(|e| {
            ForeignClientError::client_create(
                self.src_chain.id(),
                format!(
                    "failed while fetching the dst chain ({}) signer",
                    self.dst_chain.id()
                ),
                e,
            )
        })?;

        // Build client create message with the data from source chain at latest height.
        let latest_height = self.src_chain.query_latest_height().map_err(|e| {
            ForeignClientError::client_create(
                self.src_chain.id(),
                "failed while querying src chain for latest height".to_string(),
                e,
            )
        })?;

        // Calculate client state settings from the chain configurations and
        // optional user overrides.
        let src_config = self.src_chain.config().map_err(|e| {
            ForeignClientError::client_create(
                self.src_chain.id(),
                "failed while querying the source chain for configuration".to_string(),
                e,
            )
        })?;
        let dst_config = self.dst_chain.config().map_err(|e| {
            ForeignClientError::client_create(
                self.dst_chain.id(),
                "failed while querying the destination chain for configuration".to_string(),
                e,
            )
        })?;
        let settings = ClientSettings::for_create_command(options, &src_config, &dst_config);

        let client_state = self
            .src_chain
            .build_client_state(latest_height, settings)
            .map_err(|e| {
                ForeignClientError::client_create(
                    self.src_chain.id(),
                    "failed when building client state".to_string(),
                    e,
                )
            })?
            .wrap_any();

        let consensus_state = self
            .src_chain
            .build_consensus_state(
                client_state.latest_height(),
                latest_height,
                client_state.clone(),
            )
            .map_err(|e| {
                ForeignClientError::client_create(
                    self.src_chain.id(),
                    "failed while building client consensus state from src chain".to_string(),
                    e,
                )
            })?
            .wrap_any();

        //TODO Get acct_prefix
        let msg = MsgCreateAnyClient::new(client_state, consensus_state, signer)
            .map_err(ForeignClientError::client)?;

        Ok(msg)
    }

    /// Returns the identifier of the newly created client.
    pub fn build_create_client_and_send(
        &self,
        options: CreateOptions,
    ) -> Result<IbcEvent, ForeignClientError> {
        let new_msg = self.build_create_client(options)?;

        let res = self
            .dst_chain
            .send_messages_and_wait_commit(TrackedMsgs::new_single(
                new_msg.to_any(),
                "create client",
            ))
            .map_err(|e| {
                ForeignClientError::client_create(
                    self.dst_chain.id(),
                    "failed sending message to dst chain ".to_string(),
                    e,
                )
            })?;

        assert!(!res.is_empty());
        Ok(res[0].clone())
    }

    /// Sends the client creation transaction & subsequently sets the id of this ForeignClient
    fn create(&mut self) -> Result<(), ForeignClientError> {
        let event = self
            .build_create_client_and_send(CreateOptions::default())
            .map_err(|e| {
                error!("[{}]  failed CreateClient: {}", self, e);
                e
            })?;

        self.id = extract_client_id(&event)?.clone();
        info!("🍭 [{}]  => {:#?}\n", self, event);

        Ok(())
    }

    pub fn validated_client_state(
        &self,
    ) -> Result<(AnyClientState, Option<Duration>), ForeignClientError> {
        let client_state = {
            self.dst_chain
                .query_client_state(QueryClientStateRequest {
                    client_id: self.id().clone(),
                    height: Height::zero(),
                })
                .map_err(|e| {
                    ForeignClientError::client_refresh(
                        self.id().clone(),
                        "failed querying client state on dst chain".to_string(),
                        e,
                    )
                })?
        };

        if client_state.is_frozen() {
            return Err(ForeignClientError::expired_or_frozen(
                self.id().clone(),
                self.dst_chain.id(),
                "client state reports that client is frozen".into(),
            ));
        }

        match self
            .check_consensus_state_trusting_period(&client_state, &client_state.latest_height())?
        {
            ConsensusStateTrusted::NotTrusted {
                elapsed,
                network_timestamp,
                consensus_state_timestmap,
            } => {
                error!(
                    latest_height = %client_state.latest_height(),
                    network_timestmap = %network_timestamp,
                    consensus_state_timestamp = %consensus_state_timestmap,
                    elapsed = ?elapsed,
                    "[{}] client state is not valid: latest height is outside of trusting period!",
                    self
                );
                return Err(ForeignClientError::expired_or_frozen(
                    self.id().clone(),
                    self.dst_chain.id(),
                    format!(
                        "expired: time elapsed since last client update: {:?}",
                        elapsed
                    ),
                ));
            }
            ConsensusStateTrusted::Trusted { elapsed } => Ok((client_state, Some(elapsed))),
        }
    }

    /// Verifies if the consensus state at given [`Height`]
    /// is within or outside of the client's trusting period.
    fn check_consensus_state_trusting_period(
        &self,
        client_state: &AnyClientState,
        height: &Height,
    ) -> Result<ConsensusStateTrusted, ForeignClientError> {
        let _span = span!(Level::DEBUG, "check_consensus_state_trusting_period", height = %height)
            .entered();

        // Safety check
        if client_state.chain_id() != self.src_chain.id() {
            warn!("the chain id in the client state ('{}') is inconsistent with the client's source chain id ('{}')",
            client_state.chain_id(), self.src_chain.id());
        }

        let consensus_state_timestamp = self.consensus_state(*height)?.timestamp();

        let current_src_network_time = self
            .src_chain
            .query_application_status()
            .map_err(|e| {
                ForeignClientError::client_refresh(
                    self.id().clone(),
                    "failed querying the application status of source chain".to_string(),
                    e,
                )
            })?
            .timestamp;

        // Compute the duration of time elapsed since this consensus state was installed
        let elapsed = current_src_network_time
            .duration_since(&consensus_state_timestamp)
            .unwrap_or_default();

        if client_state.expired(elapsed) {
            Ok(ConsensusStateTrusted::NotTrusted {
                elapsed,
                network_timestamp: current_src_network_time,
                consensus_state_timestmap: consensus_state_timestamp,
            })
        } else {
            Ok(ConsensusStateTrusted::Trusted { elapsed })
        }
    }

    pub fn is_expired_or_frozen(&self) -> bool {
        match self.validated_client_state() {
            Ok(_) => false,
            Err(e) => e.is_expired_or_frozen_error(),
        }
    }

    pub fn refresh(&mut self) -> Result<Option<Vec<IbcEvent>>, ForeignClientError> {
        let (client_state, elapsed) = self.validated_client_state()?;

        // The refresh_window is the maximum duration
        // we can backoff between subsequent client updates.
        let refresh_window = client_state.refresh_period();

        match (elapsed, refresh_window) {
            (None, _) | (_, None) => Ok(None),
            (Some(elapsed), Some(refresh_window)) => {
                if elapsed > refresh_window {
                    info!("[{}] client requires refresh", self);
                    self.build_latest_update_client_and_send()
                        .map_or_else(Err, |ev| Ok(Some(ev)))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Wrapper for build_update_client_with_trusted.
    pub fn build_update_client(
        &self,
        target_height: Height,
    ) -> Result<Vec<Any>, ForeignClientError> {
        self.build_update_client_with_trusted(target_height, Height::zero())
    }

    /// Returns a trusted height that is lower than the target height, so
    /// that the relayer can update the client to the target height based
    /// on the returned trusted height.
    fn solve_trusted_height(
        &self,
        target_height: Height,
        client_state: &AnyClientState,
    ) -> Result<Height, ForeignClientError> {
        let client_latest_height = client_state.latest_height();

        if client_latest_height < target_height {
            // If the latest height of the client is already lower than the
            // target height, we can simply use it.
            Ok(client_latest_height)
        } else {
            // The only time when the above is false is when for some reason,
            // the command line user wants to submit a client update at an
            // older height even when the relayer already have an up-to-date
            // client at a newer height.

            // In production, this should rarely happen unless there is another
            // relayer racing to update the client state, and that we so happen
            // to get the the latest client state that was updated between
            // the time the target height was determined, and the time
            // the client state was fetched.

            warn!("[{}] resolving trusted height from the full list of consensus state heights for target height {}; this may take a while",
                self, target_height);

            // Potential optimization: cache the list of consensus heights
            // so that subsequent fetches can be fast.
            let cs_heights = self.consensus_state_heights()?;

            // Iterate through the available consesnsus heights and find one
            // that is lower than the target height.
            cs_heights
                .into_iter()
                .find(|h| h < &target_height)
                .ok_or_else(|| {
                    ForeignClientError::missing_smaller_trusted_height(
                        self.dst_chain().id(),
                        target_height,
                    )
                })
        }
    }

    /// Validate a non-zero trusted height to make sure that there is a corresponding
    /// consensus state at the given trusted height on the destination chain's client.
    fn validate_trusted_height(
        &self,
        trusted_height: Height,
        client_state: &AnyClientState,
    ) -> Result<(), ForeignClientError> {
        if client_state.latest_height() != trusted_height {
            // There should be no need to validate a trusted height in production,
            // Since it is always fetched from some client state. The only use is
            // from the command line when the trusted height is manually specified.
            // We should consider skipping the validation entirely and only validate
            // it from the command line itself.
            self.consensus_state(trusted_height)?;
        }

        Ok(())
    }

    /// Given a client state and header it adds, if required, a delay such that the header will
    /// not be considered in the future when submitted in an update client:
    /// - determine the `dst_timestamp` as the time of the latest block on destination chain
    /// - return if `header.timestamp <= dst_timestamp + client_state.max_clock_drift`
    /// - wait for the destination chain to reach `dst_timestamp + 1`
    ///    Note: This is mostly to help with existing clients where the `max_clock_drift` did
    ///    not take into account the block time.
    /// - return error if header.timestamp < dst_timestamp + client_state.max_clock_drift
    ///
    /// Ref: https://github.com/informalsystems/ibc-rs/issues/1445.
    fn wait_for_header_validation_delay(
        &self,
        client_state: &AnyClientState,
        header: &AnyHeader,
    ) -> Result<(), ForeignClientError> {
        // Get latest height and time on destination chain
        let mut status = self.dst_chain().query_application_status().map_err(|e| {
            ForeignClientError::client_update(
                self.dst_chain.id(),
                "failed querying latest status of the destination chain".to_string(),
                e,
            )
        })?;

        let ts_adjusted = (status.timestamp + client_state.max_clock_drift()).map_err(|e| {
            ForeignClientError::client_update_timing(
                self.dst_chain.id(),
                client_state.max_clock_drift(),
                "failed to adjust timestamp of destination chain with clock drift".to_string(),
                e,
            )
        })?;

        if header.timestamp().after(&ts_adjusted) {
            // Header would be considered in the future, wait for destination chain to
            // advance to the next height.
            warn!("[{}] src header {} is after dst latest header {} + client state drift {:?}, wait for next height on {}",
                   self, header.timestamp(), status.timestamp, client_state.max_clock_drift(), self.dst_chain().id());

            let target_dst_height = status.height.increment();
            loop {
                thread::sleep(Duration::from_millis(300));
                status = self.dst_chain().query_application_status().map_err(|e| {
                    ForeignClientError::client_update(
                        self.dst_chain.id(),
                        "failed querying latest status of the destination chain".to_string(),
                        e,
                    )
                })?;

                if status.height >= target_dst_height {
                    break;
                }
            }
        }

        let next_ts_adjusted =
            (status.timestamp + client_state.max_clock_drift()).map_err(|e| {
                ForeignClientError::client_update_timing(
                    self.dst_chain.id(),
                    client_state.max_clock_drift(),
                    "failed to adjust timestamp of destination chain with clock drift".to_string(),
                    e,
                )
            })?;

        if header.timestamp().after(&next_ts_adjusted) {
            // The header is still in the future
            Err(ForeignClientError::header_in_the_future(
                self.src_chain.id(),
                header.height(),
                header.timestamp(),
                self.dst_chain.id(),
                status.height,
                status.timestamp,
                client_state.max_clock_drift(),
            ))
        } else {
            Ok(())
        }
    }

    /// Returns a vector with a message for updating the client to height `target_height`.
    /// If the client already stores a consensus state for this height, returns an empty vector.
    pub fn build_update_client_with_trusted(
        &self,
        target_height: Height,
        trusted_height: Height,
    ) -> Result<Vec<Any>, ForeignClientError> {
        let src_network_latest_height = || {
            self.src_chain().query_latest_height().map_err(|e| {
                ForeignClientError::client_create(
                    self.src_chain.id(),
                    "failed fetching src network latest height with error".to_string(),
                    e,
                )
            })
        };

        // Wait for the source network to produce block(s) & reach `target_height`.
        while src_network_latest_height()? < target_height {
            thread::sleep(Duration::from_millis(100))
        }

        // Get the latest client state on destination.
        let (client_state, _) = self.validated_client_state()?;

        let trusted_height = if trusted_height == Height::zero() {
            self.solve_trusted_height(target_height, &client_state)?
        } else {
            self.validate_trusted_height(trusted_height, &client_state)?;
            trusted_height
        };

        if trusted_height != client_state.latest_height() {
            // If we're using a trusted height that is different from the client latest height,
            // then check if the consensus state at `trusted_height` is within trusting period
            if let ConsensusStateTrusted::NotTrusted {
                elapsed,
                consensus_state_timestmap,
                network_timestamp,
            } = self.check_consensus_state_trusting_period(&client_state, &trusted_height)?
            {
                error!(
                    trusted_height = %trusted_height,
                    network_timestmap = %network_timestamp,
                    consensus_state_timestamp = %consensus_state_timestmap,
                    elapsed = ?elapsed,
                    "[{}] cannot build client update message because the provided trusted height is outside of trusting period!",
                    self
                );
                return Err(ForeignClientError::consensus_state_not_trusted(
                    trusted_height,
                    elapsed,
                ));
            }
        }

        if trusted_height >= target_height {
            warn!(
                "[{}] skipping update: trusted height ({}) >= chain target height ({})",
                self, trusted_height, target_height
            );
            return Ok(vec![]);
        }

        let (header, support) = self
            .src_chain()
            .build_header(trusted_height, target_height, client_state.clone())
            .map_err(|e| {
                ForeignClientError::client_update(
                    self.src_chain.id(),
                    "failed building header with error".to_string(),
                    e,
                )
            })?;

        let signer = self.dst_chain().get_signer().map_err(|e| {
            ForeignClientError::client_update(
                self.dst_chain.id(),
                "failed getting signer for dst chain".to_string(),
                e,
            )
        })?;

        self.wait_for_header_validation_delay(&client_state, &header)?;

        let mut msgs = vec![];

        for header in support {
            debug!(
                "[{}] MsgUpdateAnyClient for intermediate height {}",
                self,
                header.height(),
            );

            msgs.push(
                MsgUpdateAnyClient {
                    header,
                    client_id: self.id.clone(),
                    signer: signer.clone(),
                }
                .to_any(),
            );
        }

        debug!(
            "[{}] MsgUpdateAnyClient from trusted height {} to target height {}",
            self,
            trusted_height,
            header.height(),
        );

        msgs.push(
            MsgUpdateAnyClient {
                header,
                signer,
                client_id: self.id.clone(),
            }
            .to_any(),
        );

        Ok(msgs)
    }

    pub fn build_latest_update_client_and_send(&self) -> Result<Vec<IbcEvent>, ForeignClientError> {
        self.build_update_client_and_send(Height::zero(), Height::zero())
    }

    pub fn build_update_client_and_send(
        &self,
        height: Height,
        trusted_height: Height,
    ) -> Result<Vec<IbcEvent>, ForeignClientError> {
        let h = if height == Height::zero() {
            self.src_chain.query_latest_height().map_err(|e| {
                ForeignClientError::client_update(
                    self.src_chain.id(),
                    "failed while querying src chain ({}) for latest height".to_string(),
                    e,
                )
            })?
        } else {
            height
        };

        let new_msgs = self.build_update_client_with_trusted(h, trusted_height)?;
        if new_msgs.is_empty() {
            return Err(ForeignClientError::client_already_up_to_date(
                self.id.clone(),
                self.src_chain.id(),
                h,
            ));
        }

        let tm = TrackedMsgs::new_static(new_msgs, "update client");

        let events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| {
                ForeignClientError::client_update(
                    self.dst_chain.id(),
                    "failed sending message to dst chain".to_string(),
                    e,
                )
            })?;

        Ok(events)
    }

    /// Attempts to update a client using header from the latest height of its source chain.
    pub fn update(&self) -> Result<(), ForeignClientError> {
        let res = self.build_latest_update_client_and_send()?;

        debug!("[{}] client updated with return message {:?}\n", self, res);

        Ok(())
    }

    /// Retrieves the client update event that was emitted when a consensus state at the
    /// specified height was created on chain.
    /// It is possible that the event cannot be retrieved if the information is not yet available
    /// on the full node. To handle this the query is retried a few times.
    pub fn update_client_event(
        &self,
        consensus_height: Height,
    ) -> Result<Option<UpdateClient>, ForeignClientError> {
        let mut events = vec![];
        for i in 0..MAX_RETRIES {
            thread::sleep(Duration::from_millis(100));
            let result = self
                .dst_chain
                .query_txs(QueryTxRequest::Client(QueryClientEventRequest {
                    height: Height::zero(),
                    event_id: WithBlockDataType::UpdateClient,
                    client_id: self.id.clone(),
                    consensus_height,
                }))
                .map_err(|e| {
                    ForeignClientError::client_event_query(
                        self.id().clone(),
                        self.dst_chain.id(),
                        consensus_height,
                        e,
                    )
                });
            match result {
                Err(e) => {
                    error!(
                        "[{}] query_tx with error {}, retry {}/{}",
                        self,
                        e,
                        i + 1,
                        MAX_RETRIES
                    );
                    continue;
                }
                Ok(result) => {
                    events = result;
                    // Should break to prevent retrying uselessly.
                    break;
                }
            }
        }

        if events.is_empty() {
            return Ok(None);
        }

        // It is possible in theory that `query_txs` returns multiple client update events for the
        // same consensus height. This could happen when multiple client updates with same header
        // were submitted to chain. However this is not what it's observed during testing.
        // Regardless, just take the event from the first update.
        let event = events[0].clone();
        let update = downcast!(event.clone() => IbcEvent::UpdateClient).ok_or_else(|| {
            ForeignClientError::unexpected_event(
                self.id().clone(),
                self.dst_chain.id(),
                event.to_json(),
            )
        })?;
        Ok(Some(update))
    }

    /// Retrieves all consensus states for this client and sorts them in descending height
    /// order. If consensus states are not pruned on chain, then last consensus state is the one
    /// installed by the `CreateClient` operation.
    fn consensus_states(&self) -> Result<Vec<AnyConsensusStateWithHeight>, ForeignClientError> {
        let mut consensus_states = self
            .dst_chain
            .query_consensus_states(QueryConsensusStatesRequest {
                client_id: self.id.clone(),
                pagination: Some(PageRequest::all()),
            })
            .map_err(|e| {
                ForeignClientError::client_query(self.id().clone(), self.src_chain.id(), e)
            })?;
        consensus_states.sort_by_key(|a| core::cmp::Reverse(a.height));
        Ok(consensus_states)
    }

    /// Returns the consensus state at `height` or error if not found.
    fn consensus_state(&self, height: Height) -> Result<AnyConsensusState, ForeignClientError> {
        let res = self
            .dst_chain
            .query_consensus_state(QueryConsensusStateRequest {
                client_id: self.id.clone(),
                consensus_height: height,
                query_height: Height::zero(),
            })
            .map_err(|e| {
                ForeignClientError::client_consensus_query(
                    self.id.clone(),
                    self.dst_chain.id(),
                    height,
                    e,
                )
            })?;

        Ok(res)
    }

    /// Retrieves all consensus heights for this client sorted in descending
    /// order.
    fn consensus_state_heights(&self) -> Result<Vec<Height>, ForeignClientError> {
        // [TODO] Utilize query that only fetches consensus state heights
        // https://github.com/cosmos/ibc-go/issues/798
        let consensus_state_heights: Vec<Height> = self
            .consensus_states()?
            .iter()
            .map(|cs| cs.height)
            .collect();

        Ok(consensus_state_heights)
    }

    /// Checks for evidence of misbehaviour.
    /// The check starts with and `update_event` emitted by chain B (`dst_chain`) for a client update
    /// with a header from chain A (`src_chain`). The algorithm goes backwards through the headers
    /// until it gets to the first misbehaviour.
    ///
    /// The following cases are covered:
    /// 1 - fork:
    /// Assumes at least one consensus state before the fork point exists.
    /// Let existing consensus states on chain B be: [Sn,.., Sf, Sf-1, S0] with `Sf-1` being
    /// the most recent state before fork.
    /// Chain A is queried for a header `Hf'` at `Sf.height` and if it is different than the `Hf`
    /// in the event for the client update (the one that has generated `Sf` on chain), then the two
    /// headers are included in the evidence and submitted.
    /// Note that in this case the headers are different but have the same height.
    ///
    /// 2 - BFT time violation for unavailable header (a.k.a. Future Lunatic Attack or FLA):
    /// Some header with a height that is higher than the latest
    /// height on A has been accepted and a consensus state was created on B. Note that this implies
    /// that the timestamp of this header must be within the `clock_drift` of the client.
    /// Assume the client on B has been updated with `h2`(not present on/ produced by chain A)
    /// and it has a timestamp of `t2` that is at most `clock_drift` in the future.
    /// Then the latest header from A is fetched, let it be `h1`, with a timestamp of `t1`.
    /// If `t1 >= t2` then evidence of misbehavior is submitted to A.
    ///
    /// 3 - BFT time violation for existing headers (TODO):
    /// Ensure that consensus state times are monotonically increasing with height.
    ///
    /// Other notes:
    /// - the algorithm builds misbehavior at each consensus height, starting with the
    /// highest height assuming the previous one is trusted. It submits the first constructed
    /// evidence (the one with the highest height)
    /// - a lot of the logic here is derived from the behavior of the only implemented client
    /// (ics07-tendermint) and might not be general enough.
    ///
    pub fn detect_misbehaviour(
        &self,
        mut update: Option<UpdateClient>,
    ) -> Result<Option<MisbehaviourEvidence>, ForeignClientError> {
        thread::sleep(Duration::from_millis(100));
        let span_guard = update.as_ref().map(|ev| ev.consensus_height());
        let _span = span!(
            tracing::Level::DEBUG,
            "detect_misbehaviour",
            update_height = ?span_guard,
        )
        .entered();

        // Get the latest client state on destination.
        let client_state = {
            self.dst_chain()
                .query_client_state(QueryClientStateRequest {
                    client_id: self.id().clone(),
                    height: Height::zero(),
                })
                .map_err(|e| {
                    ForeignClientError::misbehaviour(
                        format!("failed querying client state on dst chain {}", self.id),
                        e,
                    )
                })?
        };

        let consensus_state_heights = if let Some(ref event) = update {
            vec![event.consensus_height()]
        } else {
            // Get the list of consensus state heights in descending order.
            // Note: If chain does not prune consensus states then the last consensus state is
            // the one installed by the `CreateClient` which does not include a header.
            // For chains that do support pruning, it is possible that the last consensus state
            // was installed by an `UpdateClient` and an event and header will be found.
            self.consensus_state_heights()?
        };

        trace!(
            "checking misbehaviour for consensus state heights (first 50 shown here): {}, total: {}",
            consensus_state_heights.iter().take(50).join(", "),
            consensus_state_heights.len()
        );

        let start_time = Instant::now();
        for target_height in consensus_state_heights {
            // Start with specified update event or the one for latest consensus height
            let update_event = if let Some(ref event) = update {
                // we are here only on the first iteration when called with `Some` update event
                event.clone()
            } else if let Some(event) = self.update_client_event(target_height)? {
                // we are here either on the first iteration with `None` initial update event or
                // subsequent iterations
                event
            } else {
                // we are here if the consensus state was installed on-chain when client was
                // created, therefore there will be no update client event
                break;
            };

            // Skip over heights higher than the update event one.
            // This can happen if a client update happened with a lower height than latest.
            if target_height > update_event.consensus_height() {
                continue;
            }

            // Ensure consensus height of the event is same as target height. This should be the
            // case as we either
            // - got the `update_event` from the `target_height` above, or
            // - an `update_event` was specified and we should eventually find a consensus state
            //   at that height
            // We break here in case we got a bogus event.
            if target_height < update_event.consensus_height() {
                break;
            }

            // No header in events, cannot run misbehavior.
            // May happen on chains running older SDKs (e.g., Akash)
            if update_event.header.is_none() {
                return Err(ForeignClientError::misbehaviour_exit(format!(
                    "could not extract header from update client event {:?} emitted by chain {:?}",
                    update_event,
                    self.dst_chain.id()
                )));
            }

            // Check for misbehaviour according to the specific source chain type.
            // In case of Tendermint client, this will also check the BFT time violation if
            // a header for the event height cannot be retrieved from the witness.
            let misbehavior = match self
                .src_chain
                .check_misbehaviour(update_event.clone(), client_state.clone())
            {
                // Misbehavior check passed.
                Ok(evidence_opt) => evidence_opt,

                // Predictable error occurred which we'll wrap.
                // This error means we cannot check for misbehavior with the provided `target_height`
                Err(e) if e.is_trusted_state_outside_trusting_period_error() => {
                    debug!(target = %target_height,
                     "exhausted checking trusted consensus states for this client; no evidence found");
                    // It's safe to stop checking for misbehavior past this `target_height`.
                    break;
                }

                // Unknown error occurred in the light client `check_misbehaviour` method.
                // Propagate.
                Err(e) => {
                    return Err(ForeignClientError::misbehaviour(
                        format!(
                            "failed to check misbehaviour for {} at consensus height {}",
                            update_event.client_id(),
                            update_event.consensus_height(),
                        ),
                        e,
                    ))
                }
            };

            if misbehavior.is_some() {
                return Ok(misbehavior);
            }

            // Exit the loop if more than MAX_MISBEHAVIOUR_CHECK_TIME was spent here.
            if start_time.elapsed() > MAX_MISBEHAVIOUR_CHECK_DURATION {
                trace!(
                    "finished misbehaviour verification after {:?}",
                    start_time.elapsed()
                );

                return Ok(None);
            }

            // Clear the update
            update = None;

            // slight backoff
            thread::sleep(Duration::from_millis(100));
        }

        trace!(
            "finished misbehaviour verification after {:?}",
            start_time.elapsed()
        );

        Ok(None)
    }

    fn submit_evidence(
        &self,
        evidence: MisbehaviourEvidence,
    ) -> Result<Vec<IbcEvent>, ForeignClientError> {
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ForeignClientError::misbehaviour(
                format!(
                    "failed getting signer for destination chain ({})",
                    self.dst_chain.id()
                ),
                e,
            )
        })?;

        let mut msgs = vec![];

        for header in evidence.supporting_headers {
            msgs.push(
                MsgUpdateAnyClient {
                    header,
                    client_id: self.id.clone(),
                    signer: signer.clone(),
                }
                .to_any(),
            );
        }

        msgs.push(
            MsgSubmitAnyMisbehaviour {
                misbehaviour: evidence.misbehaviour,
                client_id: self.id.clone(),
                signer,
            }
            .to_any(),
        );

        let tm = TrackedMsgs::new_static(msgs, "evidence");

        let events = self
            .dst_chain()
            .send_messages_and_wait_commit(tm)
            .map_err(|e| {
                ForeignClientError::misbehaviour(
                    format!(
                        "failed sending evidence to destination chain ({})",
                        self.dst_chain.id(),
                    ),
                    e,
                )
            })?;

        Ok(events)
    }

    pub fn detect_misbehaviour_and_submit_evidence(
        &self,
        update_event: Option<UpdateClient>,
    ) -> MisbehaviourResults {
        // check evidence of misbehaviour for all updates or one
        let result = match self.detect_misbehaviour(update_event.clone()) {
            Err(e) => Err(e),
            Ok(None) => Ok(vec![]), // no evidence found
            Ok(Some(detected)) => {
                error!(
                    "[{}] MISBEHAVIOUR DETECTED {}, sending evidence",
                    self, detected.misbehaviour
                );

                self.submit_evidence(detected)
            }
        };

        // Filter the errors if the detection was run for all consensus states.
        // Even if some states may have failed to verify, e.g. if they were expired, just
        // warn the user and continue.
        match result {
            Err(ForeignClientError(ForeignClientErrorDetail::MisbehaviourExit(s), _)) => {
                warn!(
                    "[{}] misbehaviour checking is being disabled: {:?}",
                    self, s
                );
                MisbehaviourResults::CannotExecute
            }
            Ok(misbehaviour_detection_result) => {
                if !misbehaviour_detection_result.is_empty() {
                    info!(
                        "[{}] evidence submission result {:?}",
                        self, misbehaviour_detection_result
                    );
                    MisbehaviourResults::EvidenceSubmitted(misbehaviour_detection_result)
                } else {
                    MisbehaviourResults::ValidClient
                }
            }
            Err(e) => match e.detail() {
                ForeignClientErrorDetail::MisbehaviourExit(s) => {
                    error!(
                        "[{}] misbehaviour checking is being disabled: {:?}",
                        self, s
                    );
                    MisbehaviourResults::CannotExecute
                }
                ForeignClientErrorDetail::ExpiredOrFrozen(_) => {
                    error!(
                        "[{}] cannot check misbehavior on frozen or expired client",
                        self
                    );
                    MisbehaviourResults::CannotExecute
                }
                _ => {
                    if update_event.is_some() {
                        MisbehaviourResults::CannotExecute
                    } else {
                        warn!("[{}] misbehaviour checking result: {:?}", self, e);
                        MisbehaviourResults::ValidClient
                    }
                }
            },
        }
    }

    pub fn map_chain<DstChain2: ChainHandle, SrcChain2: ChainHandle>(
        self,
        map_dst: impl Fn(DstChain) -> DstChain2,
        map_src: impl Fn(SrcChain) -> SrcChain2,
    ) -> ForeignClient<DstChain2, SrcChain2> {
        ForeignClient {
            id: self.id,
            dst_chain: map_dst(self.dst_chain),
            src_chain: map_src(self.src_chain),
        }
    }
}

#[derive(Clone, Debug)]
pub enum MisbehaviourResults {
    CannotExecute,
    EvidenceSubmitted(Vec<IbcEvent>),
    ValidClient,
    VerificationError,
}

pub fn extract_client_id(event: &IbcEvent) -> Result<&ClientId, ForeignClientError> {
    match event {
        IbcEvent::CreateClient(ev) => Ok(ev.client_id()),
        IbcEvent::UpdateClient(ev) => Ok(ev.client_id()),
        _ => Err(ForeignClientError::missing_client_id_from_event(
            event.clone(),
        )),
    }
}

/// Tests the integration of crates `relayer` plus `relayer-cli` against crate `ibc`. These tests
/// exercise various client methods (create, update, ForeignClient::new) using locally-running
/// instances of chains built using `MockChain`.
#[cfg(test)]
mod test {
    use alloc::sync::Arc;
    use core::str::FromStr;

    use test_log::test;
    use tokio::runtime::Runtime as TokioRuntime;

    use ibc::core::ics24_host::identifier::ClientId;
    use ibc::events::IbcEvent;
    use ibc::Height;

    use crate::chain::handle::{BaseChainHandle, ChainHandle};
    use crate::chain::mock::test_utils::get_basic_chain_config;
    use crate::chain::mock::MockChain;
    use crate::chain::requests::QueryClientStateRequest;
    use crate::chain::runtime::ChainRuntime;
    use crate::foreign_client::ForeignClient;

    /// Basic test for the `build_create_client_and_send` method.
    #[test]
    fn create_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let a_chain =
            ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(a_cfg, rt.clone()).unwrap();
        let b_chain = ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(b_cfg, rt).unwrap();
        let a_client =
            ForeignClient::restore(ClientId::default(), a_chain.clone(), b_chain.clone());

        let b_client = ForeignClient::restore(ClientId::default(), b_chain, a_chain);

        // Create the client on chain a
        let res = a_client.build_create_client_and_send(Default::default());
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );
        assert!(matches!(res.unwrap(), IbcEvent::CreateClient(_)));

        // Create the client on chain b
        let res = b_client.build_create_client_and_send(Default::default());
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
        assert!(matches!(res.unwrap(), IbcEvent::CreateClient(_)));
    }

    /// Basic test for the `build_update_client_and_send` & `build_create_client_and_send` methods.
    #[test]
    fn update_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let a_client_id = ClientId::from_str("client_on_a_forb").unwrap();

        // The number of ping-pong iterations
        let num_iterations = 3;

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let a_chain =
            ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(a_cfg, rt.clone()).unwrap();
        let b_chain = ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(b_cfg, rt).unwrap();
        let mut a_client = ForeignClient::restore(a_client_id, a_chain.clone(), b_chain.clone());

        let mut b_client =
            ForeignClient::restore(ClientId::default(), b_chain.clone(), a_chain.clone());

        // This action should fail because no client exists (yet)
        let res = a_client.build_latest_update_client_and_send();
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail (no client existed)"
        );

        // Remember b's height.
        let b_height_start = b_chain.query_latest_height().unwrap();

        // Create a client on chain a
        let res = a_client.create();
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );

        // TODO: optionally add return events from `create` and assert on the event type, e.g.:
        //      assert!(matches!(res.as_ref().unwrap(), IBCEvent::CreateClient(_)));
        //      let a_client_id = extract_client_id(&res.unwrap()).unwrap().clone();

        // This should fail because the client on chain a already has the latest headers. Chain b,
        // the source chain for the client on a, is at the same height where it was when the client
        // was created, so an update should fail here.
        let res = a_client.build_latest_update_client_and_send();
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail",
        );

        // Remember b's height.
        let b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start);

        // Create a client on chain b
        let res = b_client.create();
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
        // TODO: assert return events
        //  assert!(matches!(res.as_ref().unwrap(), IBCEvent::CreateClient(_)));

        // Chain b should have advanced
        let mut b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start.increment());

        // Remember the current height of chain a
        let mut a_height_last = a_chain.query_latest_height().unwrap();

        // Now we can update both clients -- a ping pong, similar to ICS18 `client_update_ping_pong`
        for _i in 1..num_iterations {
            let res = a_client.build_latest_update_client_and_send();

            assert!(
                res.is_ok(),
                "build_update_client_and_send failed (chain a) with error: {:?}",
                res
            );

            let res = res.unwrap();
            assert!(matches!(res.last(), Some(IbcEvent::UpdateClient(_))));

            let a_height_current = a_chain.query_latest_height().unwrap();
            a_height_last = a_height_last.increment();
            assert_eq!(
                a_height_last, a_height_current,
                "after client update, chain a did not advance"
            );

            // And also update the client on chain b.
            let res = b_client.build_latest_update_client_and_send();
            assert!(
                res.is_ok(),
                "build_update_client_and_send failed (chain b) with error: {:?}",
                res
            );

            let res = res.unwrap();
            assert!(matches!(res.last(), Some(IbcEvent::UpdateClient(_))));

            let b_height_current = b_chain.query_latest_height().unwrap();
            b_height_last = b_height_last.increment();
            assert_eq!(
                b_height_last, b_height_current,
                "after client update, chain b did not advance"
            );
        }
    }

    /// Tests for `ForeignClient::new()`.
    #[test]
    fn foreign_client_create() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let a_chain =
            ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(a_cfg, rt.clone()).unwrap();
        let b_chain = ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(b_cfg, rt).unwrap();

        // Instantiate the foreign clients on the two chains.
        let res_client_on_a = ForeignClient::new(a_chain.clone(), b_chain.clone());
        assert!(
            res_client_on_a.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            res_client_on_a
        );

        let client_on_a = res_client_on_a.unwrap();
        let a_client = client_on_a.id;

        let res_client_on_b = ForeignClient::new(b_chain.clone(), a_chain.clone());
        assert!(
            res_client_on_b.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            res_client_on_b
        );
        let client_on_b = res_client_on_b.unwrap();
        let b_client = client_on_b.id;

        // Now that the clients exists, we should be able to query its state
        let b_client_state = b_chain.query_client_state(QueryClientStateRequest {
            client_id: b_client,
            height: Height::default(),
        });
        assert!(
            b_client_state.is_ok(),
            "Client query (on chain b) failed with error: {:?}",
            b_client_state
        );

        let a_client_state = a_chain.query_client_state(QueryClientStateRequest {
            client_id: a_client,
            height: Height::default(),
        });
        assert!(
            a_client_state.is_ok(),
            "Client query (on chain a) failed with error: {:?}",
            a_client_state
        );
    }

    /// Tests for `ForeignClient::update()`.
    #[test]
    fn foreign_client_update() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let mut _a_client_id = ClientId::from_str("client_on_a_forb").unwrap();
        let mut _b_client_id = ClientId::from_str("client_on_b_fora").unwrap();

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let a_chain =
            ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(a_cfg, rt.clone()).unwrap();
        let b_chain = ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(b_cfg, rt).unwrap();

        // Instantiate the foreign clients on the two chains.
        let client_on_a_res = ForeignClient::new(a_chain.clone(), b_chain.clone());
        assert!(
            client_on_a_res.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            client_on_a_res
        );
        let client_on_a = client_on_a_res.unwrap();

        let client_on_b_res = ForeignClient::new(b_chain.clone(), a_chain.clone());
        assert!(
            client_on_b_res.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            client_on_b_res
        );
        let client_on_b = client_on_b_res.unwrap();

        let num_iterations = 5;

        let mut b_height_start = b_chain.query_latest_height().unwrap();
        let mut a_height_start = a_chain.query_latest_height().unwrap();

        // Update each client
        for _i in 1..num_iterations {
            let res = client_on_a.update();
            assert!(res.is_ok(), "Client update for chain a failed {:?}", res);

            // Basic check that the height of the chain advanced
            let a_height_current = a_chain.query_latest_height().unwrap();
            a_height_start = a_height_start.increment();
            assert_eq!(
                a_height_start, a_height_current,
                "after client update, chain a did not advance"
            );

            let res = client_on_b.update();
            assert!(res.is_ok(), "Client update for chain b failed {:?}", res);

            // Basic check that the height of the chain advanced
            let b_height_current = b_chain.query_latest_height().unwrap();
            b_height_start = b_height_start.increment();
            assert_eq!(
                b_height_start, b_height_current,
                "after client update, chain b did not advance"
            );
        }
    }
}
