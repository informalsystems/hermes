//! Protocol logic specific to processing ICS2 messages of type `MsgCreateAnyClient`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientEvent, ClientResult};
use crate::ics02_client::msgs::MsgCreateAnyClient;
use crate::ics24_host::identifier::ClientId;

/// The result following the successful processing of a `MsgCreateAnyClient` message. Preferably
/// this data type should be used with a qualified name `create_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgCreateAnyClient,
) -> HandlerResult<ClientResult, Error> {
    let mut output = HandlerOutput::builder();

    if ctx.client_state(&msg.client_id()).is_some() {
        return Err(Kind::ClientAlreadyExists(msg.client_id()).into());
    }

    output.log("success: no client state found");

    output.emit(ClientEvent::ClientCreated(msg.client_id()));

    Ok(output.with_result(ClientResult::Create(Result {
        client_id: msg.client_id(),
        client_type: msg.client_state().client_type(),
        client_state: msg.client_state(),
        consensus_state: msg.consensus_state(),
    })))
}

#[cfg(test)]
mod tests {
    use crate::handler::HandlerOutput;
    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::error::Kind;
    use crate::ics02_client::handler::{dispatch, ClientEvent, ClientResult};
    use crate::ics02_client::msgs::{ClientMsg, MsgCreateAnyClient};
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::ics24_host::identifier::ClientId;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::{MockClientState, MockConsensusState};
    use crate::mock_context::MockContext;
    use crate::Height;
    use std::str::FromStr;
    use std::time::Duration;

    #[test]
    fn test_create_client_ok() {
        let client_id = ClientId::from_str("mockclient").unwrap();
        let ctx = MockContext::default();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 42);

        let msg = MsgCreateAnyClient::new(
            client_id,
            MockClientState(MockHeader(height)).into(),
            MockConsensusState(MockHeader(height)).into(),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => match result {
                ClientResult::Create(create_result) => {
                    assert_eq!(create_result.client_type, ClientType::Mock);
                    assert_eq!(
                        events,
                        vec![ClientEvent::ClientCreated(msg.client_id()).into()]
                    );
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
    fn test_create_client_existing_client_state() {
        let client_id = ClientId::from_str("mockclient").unwrap();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 30);

        let ctx = MockContext::default().with_client_parametrized(
            &client_id,
            height,
            Some(ClientType::Mock),
            Some(height.increment()),
        );
        let height = Height::new(0, 30);

        let msg = MsgCreateAnyClient::new(
            client_id,
            MockClientState(MockHeader(Height {
                version_height: 42,
                ..height
            }))
            .into(),
            MockConsensusState(MockHeader(Height {
                version_height: 42,
                ..height
            }))
            .into(),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id()));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_create_client_ok_multiple() {
        let existing_client_id = ClientId::from_str("existingmockclient").unwrap();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 80);

        let ctx = MockContext::default().with_client(&existing_client_id, height);

        let create_client_msgs: Vec<MsgCreateAnyClient> = vec![
            MsgCreateAnyClient::new(
                "newmockclient1".parse().unwrap(),
                MockClientState(MockHeader(Height {
                    version_height: 42,
                    ..height
                }))
                .into(),
                MockConsensusState(MockHeader(Height {
                    version_height: 42,
                    ..height
                }))
                .into(),
                signer,
            )
            .unwrap(),
            MsgCreateAnyClient::new(
                "newmockclient2".parse().unwrap(),
                MockClientState(MockHeader(Height {
                    version_height: 42,
                    ..height
                }))
                .into(),
                MockConsensusState(MockHeader(Height {
                    version_height: 42,
                    ..height
                }))
                .into(),
                signer,
            )
            .unwrap(),
            MsgCreateAnyClient::new(
                "newmockclient3".parse().unwrap(),
                MockClientState(MockHeader(Height {
                    version_height: 50,
                    ..height
                }))
                .into(),
                MockConsensusState(MockHeader(Height {
                    version_height: 50,
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
                    events,
                    log,
                }) => match result {
                    ClientResult::Create(create_res) => {
                        assert_eq!(create_res.client_type, msg.client_state().client_type());
                        assert_eq!(
                            events,
                            vec![ClientEvent::ClientCreated(msg.client_id()).into()]
                        );
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
    fn test_tm_create_client_ok() {
        let client_id = ClientId::from_str("tendermint").unwrap();
        let signer = get_dummy_account_id();

        let ctx = MockContext::default();

        let tm_header = get_dummy_header();
        let tm_client_state = AnyClientState::Tendermint(ClientState {
            chain_id: tm_header.signed_header.header.chain_id.to_string(),
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            latest_height: Height::new(0, u64::from(tm_header.signed_header.header.height)),
            frozen_height: Height::zero(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
            upgrade_path: "".to_string(),
        });

        let msg = MsgCreateAnyClient::new(
            client_id,
            tm_client_state,
            AnyConsensusState::Tendermint(tm_header.consensus_state()),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => match result {
                ClientResult::Create(create_res) => {
                    assert_eq!(create_res.client_type, ClientType::Tendermint);
                    assert_eq!(
                        events,
                        vec![ClientEvent::ClientCreated(msg.client_id()).into()]
                    );
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
