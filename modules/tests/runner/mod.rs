pub mod step;

use std::collections::HashMap;
use std::fmt::Debug;
use std::time::Duration;

use ibc::ics02_client::client_consensus::AnyConsensusState;
use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::context::ClientReader;
use ibc::ics02_client::error as client_error;
use ibc::ics02_client::header::AnyHeader;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics03_connection::connection::{Counterparty, State as ConnectionState};
use ibc::ics03_connection::error as connection_error;
use ibc::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::msgs::ConnectionMsg;
use ibc::ics03_connection::version::Version;
use ibc::ics04_channel::context::ChannelReader;
use ibc::ics18_relayer::context::Ics18Context;
use ibc::ics18_relayer::error as relayer_error;
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes};
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::ics26_routing::error as routing_error;
use ibc::ics26_routing::msgs::Ics26Envelope;
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::mock::host::HostType;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::signer::Signer;
use ibc::timestamp::ZERO_DURATION;
use ibc::Height;
use step::{Action, ActionOutcome, Chain, Step};

#[derive(Debug, Clone)]
pub struct IbcTestRunner {
    // mapping from chain identifier to its context
    contexts: HashMap<ChainId, MockContext>,
}

impl IbcTestRunner {
    pub fn new() -> Self {
        Self {
            contexts: Default::default(),
        }
    }

    /// Create a `MockContext` for a given `chain_id`.
    /// Panic if a context for `chain_id` already exists.
    pub fn init_chain_context(&mut self, chain_id: String, initial_height: u64) {
        let chain_id = Self::chain_id(chain_id);
        // never GC blocks
        let max_history_size = usize::MAX;
        let ctx = MockContext::new(
            chain_id.clone(),
            HostType::Mock,
            max_history_size,
            Height::new(Self::revision(), initial_height),
        );
        assert!(self.contexts.insert(chain_id, ctx).is_none());
    }

    /// Returns a reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    pub fn chain_context(&self, chain_id: String) -> &MockContext {
        self.contexts
            .get(&Self::chain_id(chain_id))
            .expect("chain context should have been initialized")
    }

    /// Returns a mutable reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    pub fn chain_context_mut(&mut self, chain_id: String) -> &mut MockContext {
        self.contexts
            .get_mut(&Self::chain_id(chain_id))
            .expect("chain context should have been initialized")
    }

    pub fn extract_ics02_error_kind(
        ics18_result: Result<(), relayer_error::Error>,
    ) -> client_error::ErrorDetail {
        let ics18_error = ics18_result.expect_err("ICS18 error expected");
        match ics18_error.detail {
            relayer_error::ErrorDetail::TransactionFailed(e) => match e.source {
                routing_error::ErrorDetail::Ics02Client(e) => e.source,
                e => {
                    panic!("Expected Ics02Client error, instead got {:?}", e);
                }
            },
            e => {
                panic!("Expected TransactionFailed error, instead got {:?}", e);
            }
        }
    }

    pub fn extract_ics03_error_kind(
        ics18_result: Result<(), relayer_error::Error>,
    ) -> connection_error::ErrorDetail {
        let ics18_error = ics18_result.expect_err("ICS18 error expected");

        match ics18_error.detail {
            relayer_error::ErrorDetail::TransactionFailed(e) => match e.source {
                routing_error::ErrorDetail::Ics03Connection(e) => e.source,
                e => {
                    panic!("Expected Ics02Client error, instead got {:?}", e);
                }
            },
            e => {
                panic!("Expected TransactionFailed error, instead got {:?}", e);
            }
        }
    }

    pub fn chain_id(chain_id: String) -> ChainId {
        ChainId::new(chain_id, Self::revision())
    }

    pub fn revision() -> u64 {
        0
    }

    pub fn version() -> Version {
        Version::default()
    }

    pub fn versions() -> Vec<Version> {
        vec![Self::version()]
    }

    pub fn client_id(client_id: u64) -> ClientId {
        ClientId::new(ClientType::Mock, client_id)
            .expect("it should be possible to create the client identifier")
    }

    pub fn connection_id(connection_id: u64) -> ConnectionId {
        ConnectionId::new(connection_id)
    }

    pub fn height(height: u64) -> Height {
        Height::new(Self::revision(), height)
    }

    fn mock_header(height: u64) -> MockHeader {
        MockHeader::new(Self::height(height))
    }

    pub fn header(height: u64) -> AnyHeader {
        AnyHeader::Mock(Self::mock_header(height))
    }

    pub fn client_state(height: u64) -> AnyClientState {
        AnyClientState::Mock(MockClientState(Self::mock_header(height)))
    }

    pub fn consensus_state(height: u64) -> AnyConsensusState {
        AnyConsensusState::Mock(MockConsensusState(Self::mock_header(height)))
    }

    fn signer() -> Signer {
        Signer::new("")
    }

    pub fn counterparty(client_id: u64, connection_id: Option<u64>) -> Counterparty {
        let client_id = Self::client_id(client_id);
        let connection_id = connection_id.map(Self::connection_id);
        let prefix = Self::commitment_prefix();
        Counterparty::new(client_id, connection_id, prefix)
    }

    pub fn delay_period() -> Duration {
        ZERO_DURATION
    }

    pub fn commitment_prefix() -> CommitmentPrefix {
        vec![0].into()
    }

    pub fn commitment_proof_bytes() -> CommitmentProofBytes {
        vec![0].into()
    }

    pub fn consensus_proof(height: u64) -> ConsensusProof {
        let consensus_proof = Self::commitment_proof_bytes();
        let consensus_height = Self::height(height);
        ConsensusProof::new(consensus_proof, consensus_height)
            .expect("it should be possible to create the consensus proof")
    }

    pub fn proofs(height: u64) -> Proofs {
        let object_proof = Self::commitment_proof_bytes();
        let client_proof = None;
        let consensus_proof = Some(Self::consensus_proof(height));
        let other_proof = None;
        let height = Self::height(height);
        Proofs::new(
            object_proof,
            client_proof,
            consensus_proof,
            other_proof,
            height,
        )
        .expect("it should be possible to create the proofs")
    }

    /// Check that chain heights match the ones in the model.
    pub fn validate_chains(&self) -> bool {
        self.contexts.values().all(|ctx| ctx.validate().is_ok())
    }

    /// Check that chain states match the ones in the model.
    pub fn check_chain_states(&self, chains: HashMap<String, Chain>) -> bool {
        chains.into_iter().all(|(chain_id, chain)| {
            let ctx = self.chain_context(chain_id);
            // check that heights match
            let heights_match = ctx.query_latest_height() == Self::height(chain.height);

            // check that clients match
            let clients_match = chain.clients.into_iter().all(|(client_id, client)| {
                // compute the highest consensus state in the model and check
                // that it matches the client state
                let client_state = ClientReader::client_state(ctx, &Self::client_id(client_id));
                let client_state_matches = match client.heights.iter().max() {
                    Some(max_height) => {
                        // if the model has consensus states (encoded simply as
                        // heights in the model), then the highest one should
                        // match the height in the client state
                        client_state.is_some()
                            && client_state.unwrap().latest_height() == Self::height(*max_height)
                    }
                    None => {
                        // if the model doesn't have any consensus states
                        // (heights), then the client state should not exist
                        client_state.is_none()
                    }
                };

                // check that each consensus state from the model exists
                // TODO: check that no other consensus state exists (i.e. the
                //       only existing consensus states are those in that also
                //       exist in the model)
                let consensus_states_match = client.heights.into_iter().all(|height| {
                    ctx.consensus_state(&Self::client_id(client_id), Self::height(height))
                        .is_some()
                });

                client_state_matches && consensus_states_match
            });

            // check that connections match
            let connections_match =
                chain
                    .connections
                    .into_iter()
                    .all(|(connection_id, connection)| {
                        if connection.state == ConnectionState::Uninitialized {
                            // if the connection has not yet been initialized, then
                            // there's nothing to check
                            true
                        } else if let Some(connection_end) =
                            ctx.connection_end(&Self::connection_id(connection_id))
                        {
                            // states must match
                            let states_match = *connection_end.state() == connection.state;

                            // client ids must match
                            let client_ids = *connection_end.client_id()
                                == Self::client_id(connection.client_id.unwrap());

                            // counterparty client ids must match
                            let counterparty_client_ids =
                                *connection_end.counterparty().client_id()
                                    == Self::client_id(connection.counterparty_client_id.unwrap());

                            // counterparty connection ids must match
                            let counterparty_connection_ids =
                                connection_end.counterparty().connection_id()
                                    == connection
                                        .counterparty_connection_id
                                        .map(Self::connection_id)
                                        .as_ref();

                            states_match
                                && client_ids
                                && counterparty_client_ids
                                && counterparty_connection_ids
                        } else {
                            // if the connection exists in the model, then it must
                            // also exist in the implementation; in this case it
                            // doesn't, so we fail the verification
                            false
                        }
                    });

            heights_match && clients_match && connections_match
        })
    }

    pub fn apply(&mut self, action: Action) -> Result<(), relayer_error::Error> {
        match action {
            Action::None => panic!("unexpected action type"),
            Action::Ics02CreateClient {
                chain_id,
                client_state,
                consensus_state,
            } => {
                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = Ics26Envelope::Ics2Msg(ClientMsg::CreateClient(MsgCreateAnyClient {
                    client_state: Self::client_state(client_state),
                    consensus_state: Self::consensus_state(consensus_state),
                    signer: Self::signer(),
                }));
                ctx.deliver(msg)
            }
            Action::Ics02UpdateClient {
                chain_id,
                client_id,
                header,
            } => {
                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = Ics26Envelope::Ics2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: Self::client_id(client_id),
                    header: Self::header(header),
                    signer: Self::signer(),
                }));
                ctx.deliver(msg)
            }
            Action::Ics03ConnectionOpenInit {
                chain_id,
                client_id,
                counterparty_chain_id: _,
                counterparty_client_id,
            } => {
                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenInit(
                    MsgConnectionOpenInit {
                        client_id: Self::client_id(client_id),
                        counterparty: Self::counterparty(counterparty_client_id, None),
                        version: Self::version(),
                        delay_period: Self::delay_period(),
                        signer: Self::signer(),
                    },
                ));
                ctx.deliver(msg)
            }
            Action::Ics03ConnectionOpenTry {
                chain_id,
                previous_connection_id,
                client_id,
                client_state,
                counterparty_chain_id: _,
                counterparty_client_id,
                counterparty_connection_id,
            } => {
                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    MsgConnectionOpenTry {
                        previous_connection_id: previous_connection_id.map(Self::connection_id),
                        client_id: Self::client_id(client_id),
                        // TODO: is this ever needed?
                        client_state: None,
                        counterparty: Self::counterparty(
                            counterparty_client_id,
                            Some(counterparty_connection_id),
                        ),
                        counterparty_versions: Self::versions(),
                        proofs: Self::proofs(client_state),
                        delay_period: Self::delay_period(),
                        signer: Self::signer(),
                    },
                )));
                ctx.deliver(msg)
            }
            Action::Ics03ConnectionOpenAck {
                chain_id,
                connection_id,
                client_state,
                counterparty_chain_id: _,
                counterparty_connection_id,
            } => {
                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenAck(Box::new(
                    MsgConnectionOpenAck {
                        connection_id: Self::connection_id(connection_id),
                        counterparty_connection_id: Self::connection_id(counterparty_connection_id),
                        // TODO: is this ever needed?
                        client_state: None,
                        proofs: Self::proofs(client_state),
                        version: Self::version(),
                        signer: Self::signer(),
                    },
                )));
                ctx.deliver(msg)
            }
            Action::Ics03ConnectionOpenConfirm {
                chain_id,
                connection_id,
                client_state,
                counterparty_chain_id: _,
                counterparty_connection_id: _,
            } => {
                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenConfirm(
                    MsgConnectionOpenConfirm {
                        connection_id: Self::connection_id(connection_id),
                        proofs: Self::proofs(client_state),
                        signer: Self::signer(),
                    },
                ));
                ctx.deliver(msg)
            }
        }
    }
}

impl modelator::runner::TestRunner<Step> for IbcTestRunner {
    fn initial_step(&mut self, step: Step) -> bool {
        assert_eq!(step.action, Action::None, "unexpected action type");
        assert_eq!(
            step.action_outcome,
            ActionOutcome::None,
            "unexpected action outcome"
        );
        // initiliaze all chains
        for (chain_id, chain) in step.chains {
            self.init_chain_context(chain_id, chain.height);
        }
        true
    }

    fn next_step(&mut self, step: Step) -> bool {
        let result = self.apply(step.action);
        let outcome_matches = match step.action_outcome {
            ActionOutcome::None => panic!("unexpected action outcome"),
            ActionOutcome::Ics02CreateOk => result.is_ok(),
            ActionOutcome::Ics02UpdateOk => result.is_ok(),
            ActionOutcome::Ics02ClientNotFound => matches!(
                Self::extract_ics02_error_kind(result),
                client_error::ErrorDetail::ClientNotFound(_)
            ),
            ActionOutcome::Ics02HeaderVerificationFailure => matches!(
                Self::extract_ics02_error_kind(result),
                client_error::ErrorDetail::HeaderVerificationFailure(_)
            ),
            ActionOutcome::Ics03ConnectionOpenInitOk => result.is_ok(),
            ActionOutcome::Ics03MissingClient => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::MissingClient(_)
            ),
            ActionOutcome::Ics03ConnectionOpenTryOk => result.is_ok(),
            ActionOutcome::Ics03InvalidConsensusHeight => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::InvalidConsensusHeight(_)
            ),
            ActionOutcome::Ics03ConnectionNotFound => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::ConnectionNotFound(_)
            ),
            ActionOutcome::Ics03ConnectionMismatch => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::ConnectionMismatch(_)
            ),
            ActionOutcome::Ics03MissingClientConsensusState => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::MissingClientConsensusState(_)
            ),
            ActionOutcome::Ics03InvalidProof => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::InvalidProof(_)
            ),
            ActionOutcome::Ics03ConnectionOpenAckOk => result.is_ok(),
            ActionOutcome::Ics03UninitializedConnection => matches!(
                Self::extract_ics03_error_kind(result),
                connection_error::ErrorDetail::UninitializedConnection(_)
            ),
            ActionOutcome::Ics03ConnectionOpenConfirmOk => result.is_ok(),
        };
        // also check the state of chains
        outcome_matches && self.validate_chains() && self.check_chain_states(step.chains)
    }
}
