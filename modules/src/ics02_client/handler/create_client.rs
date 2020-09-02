use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClient, ClientDef};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::ClientEvent;
use crate::ics02_client::msgs::MsgCreateAnyClient;
use crate::ics24_host::identifier::ClientId;

#[derive(Debug)]
pub struct CreateClientResult<CD: ClientDef> {
    client_id: ClientId,
    client_type: ClientType,
    client_state: CD::ClientState,
    consensus_state: CD::ConsensusState,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgCreateAnyClient<AnyClient>,
) -> HandlerResult<CreateClientResult<AnyClient>, Error> {
    let mut output = HandlerOutput::builder();

    let MsgCreateAnyClient {
        client_id,
        client_type,
        client_state,
        consensus_state,
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

pub fn keep(
    keeper: &mut dyn ClientKeeper,
    result: CreateClientResult<AnyClient>,
) -> Result<(), Error> {
    keeper.store_client_type(result.client_id.clone(), result.client_type)?;
    keeper.store_client_state(result.client_id.clone(), result.client_state)?;
    keeper.store_consensus_state(result.client_id, result.consensus_state)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ics02_client::context_mock::MockClientContext;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::ics07_tendermint::msgs::create_client::MsgCreateClient;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::{MockClientState, MockConsensusState};
    use std::str::FromStr;
    use std::time::Duration;
    use tendermint::block::Height;

    #[test]
    fn test_create_client_ok() {
        let client_id: ClientId = "mockclient".parse().unwrap();
        let reader = MockClientContext::new(&client_id);

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Mock,
            client_state: MockClientState(MockHeader(Height(42))).into(),
            consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
        };

        let output = process(&reader, msg.clone());

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
        let client_id: ClientId = "mockclient".parse().unwrap();
        let mut reader = MockClientContext::new(&client_id);
        reader.with_client_type(ClientType::Mock);

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Mock,
            client_state: MockClientState(MockHeader(Height(42))).into(),
            consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
        };

        let output = process(&reader, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_create_client_existing_client_state() {
        let client_id: ClientId = "mockclient".parse().unwrap();
        let mut reader = MockClientContext::new(&client_id);
        reader.with_client_state(&client_id, 30);

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Tendermint,
            client_state: MockClientState(MockHeader(Height(42))).into(),
            consensus_state: MockConsensusState(MockHeader(Height(42))).into(),
        };

        let output = process(&reader, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }
    #[test]
    fn test_tm_create_client_ok() {
        use tendermint::account::Id as AccountId;
        let client_id: ClientId = "tendermint".parse().unwrap();
        let reader = MockClientContext::new(&client_id);

        let ics_msg = MsgCreateClient {
            client_id,
            header: get_dummy_header(),
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            signer: AccountId::from_str("7C2BB42A8BE69791EC763E51F5A49BCD41E82237").unwrap(),
        };

        //let msg = ics_msg.pre_process();
        let msg = MsgCreateAnyClient {
            client_id: ics_msg.client_id().clone(),
            client_type: ics_msg.client_type(),
            client_state: ics_msg.client_state(),
            consensus_state: ics_msg.consensus_state(),
        };

        let output = process(&reader, msg.clone());

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
