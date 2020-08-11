use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client::ClientDef;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientContext, ClientEvent, ClientKeeper};
use crate::ics02_client::msgs::MsgCreateClient;
use crate::ics24_host::identifier::ClientId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CreateClientResult<CD: ClientDef> {
    client_id: ClientId,
    client_type: ClientType,
    client_state: CD::ClientState,
}

pub fn process<CD>(
    ctx: &dyn ClientContext<CD>,
    msg: MsgCreateClient<CD>,
) -> HandlerResult<CreateClientResult<CD>, Error>
where
    CD: ClientDef,
{
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

    let client_state = consensus_state.into();

    output.emit(ClientEvent::ClientCreated(client_id.clone()));

    Ok(output.with_result(CreateClientResult {
        client_id,
        client_type,
        client_state,
    }))
}

pub fn keep<CD>(
    keeper: &mut dyn ClientKeeper<CD>,
    result: CreateClientResult<CD>,
) -> Result<(), Error>
where
    CD: ClientDef,
{
    keeper.store_client_state(result.client_id.clone(), result.client_state)?;
    keeper.store_client_type(result.client_id, result.client_type)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ics02_client::header::Header;
    use crate::ics02_client::state::{ClientState, ConsensusState};
    use crate::ics23_commitment::CommitmentRoot;
    use crate::Height;
    use thiserror::Error;

    #[derive(Debug, Error)]
    enum MockError {}

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct MockHeader(u32);

    impl Header for MockHeader {
        fn client_type(&self) -> ClientType {
            todo!()
        }

        fn height(&self) -> Height {
            todo!()
        }
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct MockClientState(u32);

    impl ClientState for MockClientState {
        type ValidationError = MockError;

        fn client_id(&self) -> ClientId {
            todo!()
        }

        fn client_type(&self) -> ClientType {
            todo!()
        }

        fn get_latest_height(&self) -> Height {
            todo!()
        }

        fn is_frozen(&self) -> bool {
            todo!()
        }

        fn verify_client_consensus_state(
            &self,
            _root: &CommitmentRoot,
        ) -> Result<(), Self::ValidationError> {
            todo!()
        }
    }

    impl From<MockConsensusState> for MockClientState {
        fn from(cs: MockConsensusState) -> Self {
            Self(cs.0)
        }
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct MockConsensusState(u32);

    impl ConsensusState for MockConsensusState {
        type ValidationError = MockError;

        fn client_type(&self) -> ClientType {
            todo!()
        }

        fn height(&self) -> Height {
            todo!()
        }

        fn root(&self) -> &CommitmentRoot {
            todo!()
        }

        fn validate_basic(&self) -> Result<(), Self::ValidationError> {
            todo!()
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct MockClient;

    impl ClientDef for MockClient {
        type Header = MockHeader;
        type ClientState = MockClientState;
        type ConsensusState = MockConsensusState;
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MockClientContext {
        client_id: ClientId,
        client_state: Option<MockClientState>,
        client_type: Option<ClientType>,
        consensus_state: Option<MockConsensusState>,
    }

    impl ClientContext<MockClient> for MockClientContext {
        fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
            if client_id == &self.client_id {
                self.client_type.clone()
            } else {
                None
            }
        }

        fn client_state(&self, client_id: &ClientId) -> Option<MockClientState> {
            if client_id == &self.client_id {
                self.client_state
            } else {
                None
            }
        }

        fn consensus_state(
            &self,
            client_id: &ClientId,
            _height: Height,
        ) -> Option<MockConsensusState> {
            if client_id == &self.client_id {
                self.consensus_state
            } else {
                None
            }
        }
    }

    #[test]
    fn test_create_client_ok() {
        let client_id: ClientId = "mockclient".parse().unwrap();

        let mock = MockClientContext {
            client_id: client_id.clone(),
            client_type: None,
            client_state: None,
            consensus_state: None,
        };

        let msg = MsgCreateClient {
            client_id,
            client_type: ClientType::Tendermint,
            consensus_state: MockConsensusState(42),
        };

        let output = process(&mock, msg.clone());

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => {
                assert_eq!(result.client_type, ClientType::Tendermint);
                assert_eq!(result.client_state, MockClientState(msg.consensus_state.0));
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

        let mock = MockClientContext {
            client_id: client_id.clone(),
            client_type: Some(ClientType::Tendermint),
            client_state: None,
            consensus_state: None,
        };

        let msg = MsgCreateClient {
            client_id,
            client_type: ClientType::Tendermint,
            consensus_state: MockConsensusState(42),
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

        let mock = MockClientContext {
            client_id: client_id.clone(),
            client_type: None,
            client_state: Some(MockClientState(0)),
            consensus_state: None,
        };

        let msg = MsgCreateClient {
            client_id,
            client_type: ClientType::Tendermint,
            consensus_state: MockConsensusState(42),
        };

        let output = process(&mock, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }
}
