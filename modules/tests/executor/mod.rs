pub mod modelator;
pub mod step;

use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Debug, Display};

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::error::Kind as ICS02ErrorKind;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics03_connection::connection::Counterparty;
use ibc::ics03_connection::error::Kind as ICS03ErrorKind;
use ibc::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::msgs::ConnectionMsg;
use ibc::ics03_connection::version::Version;
use ibc::ics18_relayer::context::Ics18Context;
use ibc::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes};
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::ics26_routing::error::{Error as ICS26Error, Kind as ICS26ErrorKind};
use ibc::ics26_routing::msgs::Ics26Envelope;
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::mock::host::HostType;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::signer::Signer;
use ibc::Height;

use step::{Action, ActionOutcome, Chain, Step};

#[derive(Debug)]
pub struct IBCTestExecutor {
    // mapping from chain identifier to its context
    contexts: HashMap<ChainId, MockContext>,
}

impl IBCTestExecutor {
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

    pub fn extract_handler_error_kind<K>(ics18_result: Result<(), ICS18Error>) -> K
    where
        K: Clone + Debug + Display + Into<anomaly::BoxError> + 'static,
    {
        let ics18_error = ics18_result.expect_err("ICS18 error expected");
        assert!(matches!(
            ics18_error.kind(),
            ICS18ErrorKind::TransactionFailed
        ));
        let ics26_error = ics18_error
            .source()
            .expect("expected source in ICS18 error")
            .downcast_ref::<ICS26Error>()
            .expect("ICS18 source should be an ICS26 error");
        assert!(matches!(
            ics26_error.kind(),
            ICS26ErrorKind::HandlerRaisedError,
        ));
        ics26_error
            .source()
            .expect("expected source in ICS26 error")
            .downcast_ref::<anomaly::Error<K>>()
            .expect("ICS26 source should be an handler error")
            .kind()
            .clone()
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

    pub fn delay_period() -> u64 {
        0
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

    /// Check that chain heights match the ones in the model.
    pub fn check_chain_heights(&self, chains: HashMap<String, Chain>) -> bool {
        chains.into_iter().all(|(chain_id, chain)| {
            let ctx = self.chain_context(chain_id);
            ctx.query_latest_height() == Self::height(chain.height)
        })
    }

    pub fn apply(&mut self, action: Action) -> Result<(), ICS18Error> {
        match action {
            Action::None => panic!("unexpected action type"),
            Action::ICS02CreateClient {
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
            Action::ICS02UpdateClient {
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
            Action::ICS03ConnectionOpenInit {
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
            Action::ICS03ConnectionOpenTry {
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
            Action::ICS03ConnectionOpenAck {
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
            Action::ICS03ConnectionOpenConfirm {
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

impl modelator::TestExecutor<Step> for IBCTestExecutor {
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
            ActionOutcome::ICS02CreateOK => result.is_ok(),
            ActionOutcome::ICS02UpdateOK => result.is_ok(),
            ActionOutcome::ICS02ClientNotFound => matches!(
                Self::extract_handler_error_kind::<ICS02ErrorKind>(result),
                ICS02ErrorKind::ClientNotFound(_)
            ),
            ActionOutcome::ICS02HeaderVerificationFailure => matches!(
                Self::extract_handler_error_kind::<ICS02ErrorKind>(result),
                ICS02ErrorKind::HeaderVerificationFailure
            ),
            ActionOutcome::ICS03ConnectionOpenInitOK => result.is_ok(),
            ActionOutcome::ICS03MissingClient => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::MissingClient(_)
            ),
            ActionOutcome::ICS03ConnectionOpenTryOK => result.is_ok(),
            ActionOutcome::ICS03InvalidConsensusHeight => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::InvalidConsensusHeight(_, _)
            ),
            ActionOutcome::ICS03ConnectionNotFound => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::ConnectionNotFound(_)
            ),
            ActionOutcome::ICS03ConnectionMismatch => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::ConnectionMismatch(_)
            ),
            ActionOutcome::ICS03MissingClientConsensusState => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::MissingClientConsensusState(_, _)
            ),
            ActionOutcome::ICS03InvalidProof => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::InvalidProof
            ),
            ActionOutcome::ICS03ConnectionOpenAckOK => result.is_ok(),
            ActionOutcome::ICS03UninitializedConnection => matches!(
                Self::extract_handler_error_kind::<ICS03ErrorKind>(result),
                ICS03ErrorKind::UninitializedConnection(_)
            ),
            ActionOutcome::ICS03ConnectionOpenConfirmOK => result.is_ok(),
        };
        // also check the state of chains
        outcome_matches && self.validate_chains() && self.check_chain_heights(step.chains)
    }
}
