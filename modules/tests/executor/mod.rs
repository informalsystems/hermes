pub mod modelator;
pub mod step;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::error::Kind as ICS02ErrorKind;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics18_relayer::context::ICS18Context;
use ibc::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics26_routing::error::{Error as ICS26Error, Kind as ICS26ErrorKind};
use ibc::ics26_routing::msgs::ICS26Envelope;
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::mock::host::HostType;
use ibc::Height;
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Debug, Display};
use step::{ActionOutcome, ActionType, Chain, Step};
use tendermint::account::Id as AccountId;

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
    fn init_chain_context(&mut self, chain_id: String, initial_height: u64) {
        let chain_id = Self::chain_id(chain_id);
        let max_history_size = 1;
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
    fn chain_context(&self, chain_id: String) -> &MockContext {
        self.contexts
            .get(&Self::chain_id(chain_id))
            .expect("chain context should have been initialized")
    }

    /// Returns a mutable reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    fn chain_context_mut(&mut self, chain_id: String) -> &mut MockContext {
        self.contexts
            .get_mut(&Self::chain_id(chain_id))
            .expect("chain context should have been initialized")
    }

    fn extract_handler_error_kind<K>(ics18_result: Result<(), ICS18Error>) -> K
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

    fn chain_id(chain_id: String) -> ChainId {
        ChainId::new(chain_id, Self::revision())
    }

    fn revision() -> u64 {
        0
    }

    fn client_id(client_id: u64) -> ClientId {
        ClientId::new(ClientType::Mock, client_id)
            .expect("it should be possible to create the client identifier")
    }

    fn height(height: u64) -> Height {
        Height::new(Self::revision(), height)
    }

    fn mock_header(height: u64) -> MockHeader {
        MockHeader(Self::height(height))
    }

    fn header(height: u64) -> AnyHeader {
        AnyHeader::Mock(Self::mock_header(height))
    }

    fn client_state(height: u64) -> AnyClientState {
        AnyClientState::Mock(MockClientState(Self::mock_header(height)))
    }

    fn consensus_state(height: u64) -> AnyConsensusState {
        AnyConsensusState::Mock(MockConsensusState(Self::mock_header(height)))
    }

    fn signer() -> AccountId {
        AccountId::new([0; 20])
    }

    /// Check that chain heights match the ones in the model.
    fn check_chain_heights(&self, chains: HashMap<String, Chain>) -> bool {
        chains.into_iter().all(|(chain_id, chain)| {
            let ctx = self.chain_context(chain_id);
            ctx.query_latest_height() == Self::height(chain.height)
        })
    }
}

impl modelator::TestExecutor<Step> for IBCTestExecutor {
    fn initial_step(&mut self, step: Step) -> bool {
        assert_eq!(
            step.action.action_type,
            ActionType::None,
            "unexpected action type"
        );
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
        let outcome_matches = match step.action.action_type {
            ActionType::None => panic!("unexpected action type"),
            ActionType::ICS02CreateClient => {
                // get action parameters
                let chain_id = step
                    .action
                    .chain_id
                    .expect("create client action should have a chain identifier");
                let client_height = step
                    .action
                    .client_height
                    .expect("create client action should have a client height");

                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = ICS26Envelope::ICS2Msg(ClientMsg::CreateClient(MsgCreateAnyClient {
                    client_state: Self::client_state(client_height),
                    consensus_state: Self::consensus_state(client_height),
                    signer: Self::signer(),
                }));
                let result = ctx.deliver(msg);

                // check the expected outcome: client create always succeeds
                match step.action_outcome {
                    ActionOutcome::ICS02CreateOK => {
                        // the implementaion matches the model if no error occurs
                        result.is_ok()
                    }
                    action => panic!("unexpected action outcome {:?}", action),
                }
            }
            ActionType::ICS02UpdateClient => {
                // get action parameters
                let chain_id = step
                    .action
                    .chain_id
                    .expect("update client action should have a chain identifier");
                let client_id = step
                    .action
                    .client_id
                    .expect("update client action should have a client identifier");
                let client_height = step
                    .action
                    .client_height
                    .expect("update client action should have a client height");

                // get chain's context
                let ctx = self.chain_context_mut(chain_id);

                // create ICS26 message and deliver it
                let msg = ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: Self::client_id(client_id),
                    header: Self::header(client_height),
                    signer: Self::signer(),
                }));
                let result = ctx.deliver(msg);

                // check the expected outcome
                match step.action_outcome {
                    ActionOutcome::ICS02UpdateOK => {
                        // the implementaion matches the model if no error occurs
                        result.is_ok()
                    }
                    ActionOutcome::ICS02ClientNotFound => {
                        let handler_error_kind =
                            Self::extract_handler_error_kind::<ICS02ErrorKind>(result);
                        // the implementaion matches the model if there's an
                        // error matching the expected outcome
                        matches!(
                            handler_error_kind,
                            ICS02ErrorKind::ClientNotFound(error_client_id)
                            if error_client_id == Self::client_id(client_id)
                        )
                    }
                    ActionOutcome::ICS02HeaderVerificationFailure => {
                        let handler_error_kind =
                            Self::extract_handler_error_kind::<ICS02ErrorKind>(result);
                        // the implementaion matches the model if there's an
                        // error matching the expected outcome
                        handler_error_kind == ICS02ErrorKind::HeaderVerificationFailure
                    }
                    action => panic!("unexpected action outcome {:?}", action),
                }
            }
        };
        // also check that chain heights match
        outcome_matches && self.check_chain_heights(step.chains)
    }
}
