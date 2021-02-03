mod modelator;
mod state;

use ibc::ics02_client::client_def::AnyHeader;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::error::Kind as ICS02ErrorKind;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics03_connection::connection::Counterparty;
use ibc::ics03_connection::error::Kind as ICS03ErrorKind;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::ConnectionMsg;
use ibc::ics03_connection::version::Version;
use ibc::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::ClientId;
use ibc::ics26_routing::error::{Error as ICS26Error, Kind as ICS26ErrorKind};
use ibc::ics26_routing::msgs::ICS26Envelope;
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::mock::host::HostType;
use ibc::Height;
use state::{ActionOutcome, ActionType, State};
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Debug, Display};
use tendermint::account::Id as AccountId;

#[derive(Debug)]
struct ICS02TestExecutor {
    // mapping from chain identifier to its context
    contexts: HashMap<String, MockContext>,
}

impl ICS02TestExecutor {
    fn new() -> Self {
        Self {
            contexts: Default::default(),
        }
    }

    /// Find the `MockContext` of a given `chain_id`.
    /// If no context is found, a new one is created.
    fn get_chain_context_or_init(&mut self, chain_id: String) -> &mut MockContext {
        self.contexts.entry(chain_id.clone()).or_insert_with(|| {
            let max_history_size = 1;
            let initial_height = 0;
            MockContext::new(
                ChainId::new(chain_id, Self::epoch()),
                HostType::Mock,
                max_history_size,
                Height::new(Self::epoch(), initial_height),
            )
        })
    }

    fn extract_handler_error_kind<K>(result: Result<(), ICS18Error>) -> K
    where
        K: Clone + Debug + Display + Into<anomaly::BoxError> + 'static,
    {
        let ics18_error = result.expect_err("ICS18 error expected");
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
            .expect("ICS26 source should be an error")
            .kind()
            .clone()
    }

    // TODO: this is sometimes called version/revision number but seems
    //       unrelated with the `Version` type below; is that so?
    fn epoch() -> u64 {
        0
    }

    fn version() -> Version {
        Version::default()
    }

    fn client_id(client_id: u64) -> ClientId {
        ClientId::new(ClientType::Mock, client_id)
            .expect("it should be possible to create the client identifier")
    }

    fn mock_header(height: u64) -> MockHeader {
        MockHeader(Height::new(Self::epoch(), height))
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

    fn counterparty(counterparty_client_id: u64) -> Counterparty {
        Counterparty::new(
            Self::client_id(counterparty_client_id),
            None,
            CommitmentPrefix(Vec::new()),
        )
    }

    fn delay_period() -> u64 {
        0
    }
}

impl modelator::TestExecutor<State> for ICS02TestExecutor {
    fn check_initial_state(&mut self, state: State) -> bool {
        assert_eq!(
            state.action.action_type,
            ActionType::Null,
            "unexpected action type"
        );
        assert_eq!(
            state.action_outcome,
            ActionOutcome::Null,
            "unexpected action outcome"
        );
        true
    }

    fn check_next_state(&mut self, state: State) -> bool {
        match state.action.action_type {
            ActionType::Null => panic!("unexpected action type"),
            ActionType::ICS02CreateClient => {
                // get action parameters
                let chain_id = state
                    .action
                    .chain_id
                    .expect("create client action should have a chain identifier");
                let height = state
                    .action
                    .height
                    .expect("create client action should have a height");

                // get chain's context
                let ctx = self.get_chain_context_or_init(chain_id);

                // create ICS26 message and deliver it
                let msg = ICS26Envelope::ICS2Msg(ClientMsg::CreateClient(MsgCreateAnyClient {
                    client_state: Self::client_state(height),
                    consensus_state: Self::consensus_state(height),
                    signer: Self::signer(),
                }));
                let result = ctx.deliver(msg);

                // check the expected outcome: client create always succeeds
                match state.action_outcome {
                    ActionOutcome::ICS02CreateOK => {
                        // the implementaion matches the model if no error occurs
                        result.is_ok()
                    }
                    action => panic!("unexpected action outcome {:?}", action),
                }
            }
            ActionType::ICS02UpdateClient => {
                // get action parameters
                let chain_id = state
                    .action
                    .chain_id
                    .expect("update client action should have a chain identifier");
                let client_id = state
                    .action
                    .client_id
                    .expect("update client action should have a client identifier");
                let height = state
                    .action
                    .height
                    .expect("update client action should have a height");

                // get chain's context
                let ctx = self.get_chain_context_or_init(chain_id);

                // create ICS26 message and deliver it
                let msg = ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: Self::client_id(client_id),
                    header: Self::header(height),
                    signer: Self::signer(),
                }));
                let result = ctx.deliver(msg);

                // check the expected outcome
                match state.action_outcome {
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
                            ICS02ErrorKind::ClientNotFound(id) if id == Self::client_id(client_id)
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
            ActionType::ICS03ConnectionOpenInit => {
                // get action parameters
                let chain_id = state
                    .action
                    .chain_id
                    .expect("connection open init action should have a chain identifier");
                let client_id = state
                    .action
                    .client_id
                    .expect("connection open init action should have a client identifier");
                let counterparty_client_id = state.action.counterparty_client_id.expect(
                    "connection open init action should have a counterparty client identifier",
                );

                // get chain's context
                let ctx = self.get_chain_context_or_init(chain_id);

                // create ICS26 message and deliver it
                let msg = ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenInit(
                    MsgConnectionOpenInit {
                        client_id: Self::client_id(client_id),
                        counterparty: Self::counterparty(counterparty_client_id),
                        version: Self::version(),
                        delay_period: Self::delay_period(),
                        signer: Self::signer(),
                    },
                ));
                let result = ctx.deliver(msg);

                // check the expected outcome
                match state.action_outcome {
                    ActionOutcome::ICS03ConnectionOpenInitOK => {
                        // the implementaion matches the model if no error occurs
                        result.is_ok()
                    }
                    ActionOutcome::ICS03MissingClient => {
                        let handler_error_kind =
                            Self::extract_handler_error_kind::<ICS03ErrorKind>(result);
                        // the implementaion matches the model if there's an
                        // error matching the expected outcome
                        matches!(
                            handler_error_kind,
                            ICS03ErrorKind::MissingClient(id) if id == Self::client_id(client_id)
                        )
                    }
                    action => panic!("unexpected action outcome {:?}", action),
                }
            }
        }
    }
}

const TESTS_DIR: &str = "tests/support/model_based";

#[test]
fn main() {
    let tests = vec![
        "ICS02UpdateOKTest",
        "ICS02HeaderVerificationFailureTest",
        "ICS03ConnectionOpenInitOKTest",
        "ICS03MissingClientTest",
    ];

    for test in tests {
        let path = format!("{}/{}.json", TESTS_DIR, test);
        let test_executor = ICS02TestExecutor::new();
        // we should be able to just return the `Result` once the following issue
        // is fixed: https://github.com/rust-lang/rust/issues/43301
        if let Err(e) = modelator::test_driver(test_executor, path) {
            panic!("{:?}", e);
        }
    }
}
