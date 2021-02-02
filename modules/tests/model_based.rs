mod modelator;

use serde::Deserialize;
use std::fmt::Debug;

#[derive(Debug, Clone, Deserialize)]
struct State {
    action: Action,

    #[serde(alias = "actionOutcome")]
    action_outcome: ActionOutcome,
}

#[derive(Debug, Clone, Deserialize)]
struct Action {
    #[serde(alias = "type")]
    action_type: ActionType,

    #[serde(alias = "clientId")]
    client_id: Option<u64>,

    height: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
enum ActionType {
    Null,
    CreateClient,
    UpdateClient,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
enum ActionOutcome {
    Null,
    CreateOK,
    UpdateHeightVerificationFailure,
}

struct ICS02TestExecutor;

impl modelator::TestExecutor<State> for ICS02TestExecutor {
    fn check_initial_state(&mut self, state: State) -> bool {
        let type_is_null = state.action.action_type == ActionType::Null;
        let outcome_is_null = state.action_outcome == ActionOutcome::Null;
        type_is_null && outcome_is_null
    }

    fn check_next_state(&mut self, state: State) -> bool {
        todo!()
    }
}

#[test]
fn main() {
    let path = "tests/support/model_based/test.json";
    let test_executor = ICS02TestExecutor;
    // we should be able to just return the `Result` once the following issue
    // is fixed: https://github.com/rust-lang/rust/issues/43301 
    if let Err(e) = modelator::test_driver(test_executor, path) {
        panic!("{:?}", e);
    }
}
