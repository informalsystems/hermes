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

    let MsgCreateAnyClient {
        client_id,
        client_type,
        client_state,
        consensus_state,
        signer: _,
    } = msg;

    if ctx.client_state(&client_id).is_some() {
        return Err(Kind::ClientAlreadyExists(client_id).into());
    }

    output.log("success: no client state found");

    if ctx.client_type(&client_id).is_some() {
        return Err(Kind::ClientAlreadyExists(client_id).into());
    }

    output.log("success: no client type found");

    output.emit(ClientEvent::ClientCreated(client_id.clone()));

    Ok(output.with_result(CreateClientResult {
        client_id,
        client_type,
        client_state,
        consensus_state,
    }))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;
    use tendermint::block::Height;

    use super::*;
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

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Mock,
            client_state: MockClientState(MockHeader(Height(42))).into(),
            consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
            signer,
        };

        let output = process(&ctx, msg.clone());

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => {
                assert_eq!(result.client_type, ClientType::Mock);
                assert_eq!(
                    events,
                    vec![ClientEvent::ClientCreated(msg.client_id).into()]
                );
                assert_eq!(
                    log,
                    vec![
                        "success: no client state found".to_string(),
                        "success: no client type found".to_string()
                    ]
                );
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_create_client_existing_client_type() {
        let height = Height(42);
        let client_id: ClientId = "mockclient".parse().unwrap();
        let signer = get_dummy_account_id();

        let mut ctx = MockClientContext::default();
        ctx.with_client_type(&client_id, ClientType::Mock, height);

        ctx.with_client_type(&client_id, ClientType::Tendermint, height);

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Mock,
            client_state: MockClientState(MockHeader(height)).into(),
            consensus_state: MockConsensusState(MockHeader(height)).into(),
            signer,
        };

        let output = process(&ctx, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_create_client_existing_client_state() {
        let client_id: ClientId = "mockclient".parse().unwrap();
        let signer = get_dummy_account_id();

        let mut ctx = MockClientContext::default();
        let height = Height(30);
        ctx.with_client_consensus_state(&client_id, height);

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Tendermint,
            client_state: MockClientState(MockHeader(Height(42))).into(),
            consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
            signer,
        };

        let output = process(&ctx, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_create_client_ok_multiple() {
        let existing_client_id: ClientId = "existingmockclient".parse().unwrap();
        let signer = get_dummy_account_id();
        let height = Height(80);
        let mut ctx = MockClientContext::default();
        ctx.with_client_consensus_state(&existing_client_id, height);

        let create_client_msgs: Vec<MsgCreateAnyClient> = vec![
            MsgCreateAnyClient {
                client_id: "newmockclient1".parse().unwrap(),
                client_type: ClientType::Mock,
                client_state: MockClientState(MockHeader(Height(42))).into(),
                consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
                signer,
            },
            MsgCreateAnyClient {
                client_id: "newmockclient2".parse().unwrap(),
                client_type: ClientType::Mock,
                client_state: MockClientState(MockHeader(Height(42))).into(),
                consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
                signer,
            },
            MsgCreateAnyClient {
                client_id: "newmockclient3".parse().unwrap(),
                client_type: ClientType::Tendermint,
                client_state: MockClientState(MockHeader(Height(50))).into(),
                consensus_state: MockConsensusState(MockHeader(Height(50))).into(),
                signer,
            },
        ]
        .into_iter()
        .collect();

        for msg in create_client_msgs {
            let output = process(&ctx, msg.clone());

            match output {
                Ok(HandlerOutput {
                    result,
                    events,
                    log,
                }) => {
                    assert_eq!(result.client_type, msg.client_type);
                    assert_eq!(
                        events,
                        vec![ClientEvent::ClientCreated(msg.client_id).into()]
                    );
                    assert_eq!(
                        log,
                        vec![
                            "success: no client state found".to_string(),
                            "success: no client type found".to_string()
                        ]
                    );
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
            latest_height: tm_header.signed_header.header.height,
            frozen_height: 0.into(),
        });

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Tendermint,
            client_state: tm_client_state,
            consensus_state: AnyConsensusState::Tendermint(tm_header.consensus_state()),
            signer,
        };

        let output = process(&ctx, msg.clone());

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => {
                assert_eq!(result.client_type, ClientType::Tendermint);
                assert_eq!(
                    events,
                    vec![ClientEvent::ClientCreated(msg.client_id).into()]
                );
                assert_eq!(
                    log,
                    vec![
                        "success: no client state found".to_string(),
                        "success: no client type found".to_string()
                    ]
                );
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }
}
