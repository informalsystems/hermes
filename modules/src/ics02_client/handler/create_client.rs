use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::ClientEvent;
use crate::ics02_client::msgs::MsgCreateAnyClient;
use crate::ics24_host::identifier::ClientId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CreateClientResult {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgCreateAnyClient,
) -> HandlerResult<CreateClientResult, Error> {
    let mut output = HandlerOutput::builder();

    if ctx.client_state(&msg.client_id()).is_some() {
        return Err(Kind::ClientAlreadyExists(msg.client_id()).into());
    }

    output.log("success: no client state found");

    output.emit(ClientEvent::ClientCreated(msg.client_id()));

    Ok(output.with_result(CreateClientResult {
        client_id: msg.client_id(),
        client_type: msg.client_state().client_type(),
        client_state: msg.client_state(),
        consensus_state: msg.consensus_state(),
    }))
}

#[cfg(test)]
mod tests {
    use crate::Height;
    use std::time::Duration;

    use super::*;
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::context_mock::MockClientContext;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::{MockClientState, MockConsensusState};

    #[test]
    fn test_create_client_ok() {
        let client_id: ClientId = "mockclient".parse().unwrap();
        let ctx = MockClientContext::default();

        let signer = get_dummy_account_id();

        let height = Height {
            version_number: 0,
            version_height: 42,
        };

        let msg = MsgCreateAnyClient::new(
            client_id,
            MockClientState(MockHeader(height)).into(),
            MockConsensusState(MockHeader(height)).into(),
            signer,
        )
        .unwrap();

        let output = process(&ctx, msg.clone());

        match output {
            Ok(HandlerOutput {
                result: _result,
                events,
                log,
            }) => {
                assert_eq!(
                    events,
                    vec![ClientEvent::ClientCreated(msg.client_id()).into()]
                );
                assert_eq!(log, vec!["success: no client state found".to_string()]);
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_create_client_existing_client_state() {
        let client_id: ClientId = "mockclient".parse().unwrap();
        let signer = get_dummy_account_id();

        let mut ctx = MockClientContext::default();
        let height = Height {
            version_number: 0,
            version_height: 30,
        };
        ctx.with_client(&client_id, ClientType::Mock, height);
        ctx.with_client_consensus_state(&client_id, height.increment());

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

        let output = process(&ctx, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id()));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_create_client_ok_multiple() {
        let existing_client_id: ClientId = "existingmockclient".parse().unwrap();
        let signer = get_dummy_account_id();
        let height = Height {
            version_number: 0,
            version_height: 80,
        };
        let mut ctx = MockClientContext::default();
        ctx.with_client(&existing_client_id, ClientType::Mock, height);

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
            let output = process(&ctx, msg.clone());

            match output {
                Ok(HandlerOutput {
                    result: _,
                    events,
                    log,
                }) => {
                    assert_eq!(
                        events,
                        vec![ClientEvent::ClientCreated(msg.client_id()).into()]
                    );
                    assert_eq!(log, vec!["success: no client state found".to_string()]);
                }
                Err(err) => {
                    panic!("unexpected error: {}", err);
                }
            }
        }
    }

    #[test]
    fn test_tm_create_client_ok() {
        let client_id: ClientId = "tendermint".parse().unwrap();
        let signer = get_dummy_account_id();

        let ctx = MockClientContext::default();

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

        let output = process(&ctx, msg.clone());

        match output {
            Ok(HandlerOutput {
                result: _,
                events,
                log,
            }) => {
                assert_eq!(
                    events,
                    vec![ClientEvent::ClientCreated(msg.client_id()).into()]
                );
                assert_eq!(log, vec!["success: no client state found".to_string()]);
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }
}
