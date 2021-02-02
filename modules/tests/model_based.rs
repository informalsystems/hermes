mod modelator;
mod state;

use ibc::ics02_client::client_def::AnyHeader;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::ClientId;
use ibc::ics26_routing::msgs::ICS26Envelope;
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::mock::host::HostType;
use ibc::Height;
use state::{ActionOutcome, ActionType, State};
use std::fmt::Debug;
use tendermint::account::Id as AccountId;

#[derive(Debug)]
struct ICS02TestExecutor {
    version: u64,
    ctx: MockContext,
}

impl ICS02TestExecutor {
    fn new() -> Self {
        let version = 1;
        let ctx = MockContext::new(
            ChainId::new("mock".to_string(), version),
            HostType::Mock,
            1,
            Height::new(version, 0),
        );
        // let ctx = MockContext::new(
        //     ChainId::new("mock".to_string(), cv),
        //     HostType::SyntheticTendermint,
        //     1,
        //     Height::new(cv, 0),
        // );

        Self { version, ctx }
    }
}

impl modelator::TestExecutor<State> for ICS02TestExecutor {
    fn check_initial_state(&mut self, state: State) -> bool {
        let type_is_null = state.action.action_type == ActionType::Null;
        let outcome_is_null = state.action_outcome == ActionOutcome::Null;
        type_is_null && outcome_is_null
    }

    fn check_next_state(&mut self, state: State) -> bool {
        match state.action.action_type {
            ActionType::Null => panic!("next state action type cannot be null"),
            ActionType::CreateClient => {
                // get action parameters
                let height = state
                    .action
                    .height
                    .expect("update client action should have a height");

                // create client and consensus state from parameters
                let client_state = AnyClientState::Mock(MockClientState(self.mock_header(height)));
                let consensus_state =
                    AnyConsensusState::Mock(MockConsensusState(self.mock_header(height)));

                // create dummy signer
                let signer = self.dummy_signer();

                // create ICS26 message
                let msg = ICS26Envelope::ICS2Msg(ClientMsg::CreateClient(MsgCreateAnyClient {
                    client_state,
                    consensus_state,
                    signer,
                }));
                self.ctx.deliver(msg).unwrap();
                true
            }
            ActionType::UpdateClient => {
                // TODO: rename clientId to clientCounter in the model
                // get action parameters
                let client_id = state
                    .action
                    .client_id
                    .expect("update client action should have a client identifier");
                let height = state
                    .action
                    .height
                    .expect("update client action should have a height");

                // create client id and header from action parameters
                let client_id = ClientId::new(ClientType::Mock, client_id)
                    .expect("it should be possible to create the client identifier");
                let header = AnyHeader::Mock(self.mock_header(height));

                // create dummy signer
                let signer = self.dummy_signer();

                // create ICS26 message
                let msg = ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id,
                    header,
                    signer,
                }));
                self.ctx.deliver(msg).unwrap();
                true
            }
        }
    }
}

impl ICS02TestExecutor {
    fn dummy_signer(&self) -> AccountId {
        AccountId::new([0; 20])
    }

    fn mock_header(&self, height: u64) -> MockHeader {
        MockHeader(Height::new(self.version, height))
    }
}

#[test]
fn main() {
    let path = "tests/support/model_based/test.json";
    let test_executor = ICS02TestExecutor::new();
    // we should be able to just return the `Result` once the following issue
    // is fixed: https://github.com/rust-lang/rust/issues/43301
    if let Err(e) = modelator::test_driver(test_executor, path) {
        panic!("{:?}", e);
    }
}
