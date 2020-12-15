//! Protocol logic specific to processing ICS2 messages of type `MsgCreateAnyClient`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::error::Error;
use crate::ics02_client::handler::ClientResult;
use crate::ics02_client::msgs::create_client::MsgCreateAnyClient;

/// The result following the successful processing of a `MsgCreateAnyClient` message. Preferably
/// this data type should be used with a qualified name `create_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result {
    pub client_type: ClientType,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
}

pub fn process(
    _ctx: &dyn ClientReader,
    msg: MsgCreateAnyClient,
) -> HandlerResult<ClientResult, Error> {
    let output = HandlerOutput::builder();

    Ok(output.with_result(ClientResult::Create(Result {
        client_type: msg.client_state().client_type(),
        client_state: msg.client_state(),
        consensus_state: msg.consensus_state(),
    })))
}

/// ## Why are all these tests ignored?
/// All these tests are ignored as of #451, because the logic inside `process` has been simplified
/// to the point where there's nothing to test.
/// TODO: We should consider refactoring the ICS02 handlers
/// by moving the `next_client_id` method into trait `ClientReader` (make it a deterministic & pure
/// method call) and thus generate client ids in the `process` call above. Then we re-enable tests.
#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use std::time::Duration;

    use tendermint_light_client::types::TrustThreshold;

    use crate::handler::HandlerOutput;
    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::handler::{dispatch, ClientResult};
    use crate::ics02_client::msgs::create_client::MsgCreateAnyClient;
    use crate::ics02_client::msgs::ClientMsg;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics24_host::identifier::ClientId;
    use crate::mock::client_state::{MockClientState, MockConsensusState};
    use crate::mock::context::MockContext;
    use crate::mock::header::MockHeader;
    use crate::Height;

    use crate::ics07_tendermint::header::test_util::get_dummy_tendermint_header;
    use crate::test_utils::get_dummy_account_id;
    use std::convert::TryInto;

    #[test]
    #[ignore = "handlers simplified (#451), nothing left to test"]
    fn test_create_client_ok() {
        let ctx = MockContext::default();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 42);

        let msg = MsgCreateAnyClient::new(
            MockClientState(MockHeader(height)).into(),
            MockConsensusState(MockHeader(height)).into(),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg));

        match output {
            Ok(HandlerOutput {
                result,
                log,
                events: _,
            }) => match result {
                ClientResult::Create(create_result) => {
                    assert_eq!(create_result.client_type, ClientType::Mock);
                    assert_eq!(log, vec!["success: no client state found".to_string(),]);
                }
                _ => {
                    panic!("unexpected result type: expected ClientResult::CreateResult!");
                }
            },
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    #[ignore = "handlers simplified (#451), nothing left to test"]
    fn test_create_client_ok_multiple() {
        let existing_client_id = ClientId::from_str("existingmockclient").unwrap();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 80);

        let ctx = MockContext::default().with_client(&existing_client_id, height);

        let create_client_msgs: Vec<MsgCreateAnyClient> = vec![
            MsgCreateAnyClient::new(
                MockClientState(MockHeader(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                MockConsensusState(MockHeader(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                signer,
            )
            .unwrap(),
            MsgCreateAnyClient::new(
                MockClientState(MockHeader(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                MockConsensusState(MockHeader(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                signer,
            )
            .unwrap(),
            MsgCreateAnyClient::new(
                MockClientState(MockHeader(Height {
                    revision_height: 50,
                    ..height
                }))
                .into(),
                MockConsensusState(MockHeader(Height {
                    revision_height: 50,
                    ..height
                }))
                .into(),
                signer,
            )
            .unwrap(),
        ]
        .into_iter()
        .collect();

        for msg in create_client_msgs {
            let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

            match output {
                Ok(HandlerOutput {
                    result,
                    log,
                    events: _,
                }) => match result {
                    ClientResult::Create(create_res) => {
                        assert_eq!(create_res.client_type, msg.client_state().client_type());
                        assert_eq!(log, vec!["success: no client state found".to_string(),]);
                    }
                    _ => {
                        panic!("expected result of type ClientResult::CreateResult");
                    }
                },
                Err(err) => {
                    panic!("unexpected error: {}", err);
                }
            }
        }
    }

    #[test]
    #[ignore = "handlers simplified (#451), nothing left to test"]
    fn test_tm_create_client_ok() {
        let signer = get_dummy_account_id();

        let ctx = MockContext::default();

        let tm_header = get_dummy_tendermint_header();
        let tm_client_state = AnyClientState::Tendermint(ClientState {
            chain_id: tm_header.chain_id.to_string(),
            trust_level: TrustThreshold {
                numerator: 1,
                denominator: 3,
            },
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            latest_height: Height::new(0, u64::from(tm_header.height)),
            frozen_height: Height::zero(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
            upgrade_path: vec!["".to_string()],
        });

        let msg = MsgCreateAnyClient::new(
            tm_client_state,
            AnyConsensusState::Tendermint(tm_header.try_into().unwrap()),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg));

        match output {
            Ok(HandlerOutput {
                result,
                log,
                events: _,
            }) => match result {
                ClientResult::Create(create_res) => {
                    assert_eq!(create_res.client_type, ClientType::Tendermint);
                    assert_eq!(log, vec!["success: no client state found".to_string(),]);
                }
                _ => {
                    panic!("expected result of type ClientResult::CreateResult");
                }
            },
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }
}
