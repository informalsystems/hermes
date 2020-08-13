#![allow(unreachable_code, unused_variables)]

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientEvent, ClientKeeper, ClientReader};
use crate::ics02_client::msgs::MsgCreateClient;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics24_host::identifier::ClientId;

#[derive(Debug)]
pub struct CreateClientResult {
    client_id: ClientId,
    client_type: ClientType,
    client_state: Box<dyn ClientState>,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgCreateClient,
) -> HandlerResult<CreateClientResult, Error> {
    let mut output = HandlerOutput::builder();

    let MsgCreateClient {
        client_id,
        client_type,
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

    let client_state = todo!(); // CD::new_client_state(&consensus_state);

    output.emit(ClientEvent::ClientCreated(client_id.clone()));

    Ok(output.with_result(CreateClientResult {
        client_id,
        client_type,
        client_state,
    }))
}

pub fn keep(keeper: &mut dyn ClientKeeper, result: CreateClientResult) -> Result<(), Error> {
    keeper.store_client_state(result.client_id.clone(), result.client_state.as_ref())?;
    keeper.store_client_type(result.client_id, result.client_type)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ics02_client::header::Header;
    use crate::ics02_client::mocks::*;
    use crate::ics02_client::state::{ClientState, ConsensusState};
    use crate::ics23_commitment::CommitmentRoot;
    use crate::Height;
    use thiserror::Error;

    #[test]
    fn test_create_client_ok() {
        let client_id: ClientId = "mockclient".parse().unwrap();

        let mock = MockClientReader {
            client_id: client_id.clone(),
            client_type: None,
            client_state: None,
            consensus_state: None,
        };

        let msg = MsgCreateClient {
            client_id,
            client_type: ClientType::Tendermint,
            consensus_state: Box::new(MockConsensusState(42)),
        };

        let output = process(&mock, msg.clone());

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => {
                assert_eq!(result.client_type, ClientType::Tendermint);
                // assert_eq!(
                //     result.client_state.as_ref().0,
                //     msg.consensus_state.as_ref().0
                // );
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

        let mock = MockClientReader {
            client_id: client_id.clone(),
            client_type: Some(ClientType::Tendermint),
            client_state: None,
            consensus_state: None,
        };

        let msg = MsgCreateClient {
            client_id,
            client_type: ClientType::Tendermint,
            consensus_state: Box::new(MockConsensusState(42)),
        };

        let output = process(&mock, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_create_client_existing_client_state() {
        let client_id: ClientId = "mockclient".parse().unwrap();

        let mock = MockClientReader {
            client_id: client_id.clone(),
            client_type: None,
            client_state: Some(MockClientState(0)),
            consensus_state: None,
        };

        let msg = MsgCreateClient {
            client_id,
            client_type: ClientType::Tendermint,
            consensus_state: Box::new(MockConsensusState(42)),
        };

        let output = process(&mock, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }
}
