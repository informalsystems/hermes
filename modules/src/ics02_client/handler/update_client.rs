use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client::ClientDef;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientEvent, ClientKeeper, ClientReader};
use crate::ics02_client::msgs::MsgUpdateClient;
use crate::ics02_client::state::ClientState;
use crate::ics24_host::identifier::ClientId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpdateClientResult<C: ClientDef> {
    client_id: ClientId,
    client_state: C::ClientState,
    consensus_state: C::ConsensusState,
}

pub fn process<CD>(
    ctx: &dyn ClientReader<CD>,
    msg: MsgUpdateClient<CD>,
) -> HandlerResult<UpdateClientResult<CD>, Error>
where
    CD: ClientDef,
{
    let mut output = HandlerOutput::builder();

    let MsgUpdateClient { client_id, header } = msg;

    let _client_type = ctx
        .client_type(&client_id)
        .ok_or_else(|| Kind::ClientNotFound(client_id.clone()))?;

    let mut client_state = ctx
        .client_state(&client_id)
        .ok_or_else(|| Kind::ClientNotFound(client_id.clone()))?;

    let latest_height = client_state.get_latest_height();
    let consensus_state = ctx
        .consensus_state(&client_id, latest_height)
        .ok_or_else(|| Kind::ConsensusStateNotFound(client_id.clone(), latest_height))?;

    CD::check_validity_and_update_state(&mut client_state, &consensus_state, &header).unwrap(); // FIXME

    output.emit(ClientEvent::ClientUpdated(client_id.clone()));

    Ok(output.with_result(UpdateClientResult {
        client_id,
        client_state,
        consensus_state,
    }))
}

pub fn keep<CD>(
    keeper: &mut dyn ClientKeeper<CD>,
    result: UpdateClientResult<CD>,
) -> Result<(), Error>
where
    CD: ClientDef,
{
    keeper.store_client_state(result.client_id.clone(), result.client_state)?;
    keeper.store_consensus_state(result.client_id, result.consensus_state)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ics02_client::client_type::ClientType;
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

    fn new_client_state(
        client_state: &MockClientState,
        consensus_state: &MockConsensusState,
        header: &MockHeader,
    ) -> MockClientState {
        MockClientState(client_state.0 * 17 + consensus_state.0 * 13 + header.0 * 7)
    }

    impl ClientDef for MockClient {
        type Error = MockError;
        type Header = MockHeader;
        type ClientState = MockClientState;
        type ConsensusState = MockConsensusState;

        fn check_validity_and_update_state(
            client_state: &mut MockClientState,
            consensus_state: &MockConsensusState,
            header: &MockHeader,
        ) -> Result<(), Self::Error> {
            client_state.0 = new_client_state(client_state, consensus_state, header).0;
            Ok(())
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MockClientContext {
        client_state: Option<MockClientState>,
        client_type: Option<ClientType>,
        consensus_state: Option<MockConsensusState>,
    }

    impl ClientReader<MockClient> for MockClientContext {
        fn client_type(&self, _client_id: &ClientId) -> Option<ClientType> {
            self.client_type.clone()
        }

        fn client_state(&self, _client_id: &ClientId) -> Option<MockClientState> {
            self.client_state
        }

        fn consensus_state(
            &self,
            _client_id: &ClientId,
            _height: Height,
        ) -> Option<MockConsensusState> {
            self.consensus_state
        }
    }

    #[test]
    fn test_update_client_ok() {
        let mock = MockClientContext {
            client_type: None,
            client_state: None,
            consensus_state: None,
        };

        let msg = MsgUpdateClient {
            client_id: "mockclient".parse().unwrap(),
            header: MockHeader(1),
        };

        let output = process(&mock, msg.clone());

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => {
                assert_eq!(result.client_state, MockClientState(0));
                assert_eq!(
                    events,
                    vec![ClientEvent::ClientUpdated(msg.client_id).into()]
                );
                assert!(log.is_empty());
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_client_existing_client_type() {
        let mock = MockClientContext {
            client_type: Some(ClientType::Tendermint),
            client_state: None,
            consensus_state: None,
        };

        let msg = MsgUpdateClient {
            client_id: "mockclient".parse().unwrap(),
            header: MockHeader(1),
        };

        let output = process(&mock, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }

    #[test]
    fn test_update_client_existing_client_state() {
        let mock = MockClientContext {
            client_type: None,
            client_state: Some(MockClientState(11)),
            consensus_state: None,
        };

        #[allow(unreachable_code)]
        let msg = MsgUpdateClient {
            client_id: "mockclient".parse().unwrap(),
            header: MockHeader(42),
        };

        let output = process(&mock, msg.clone());

        if let Err(err) = output {
            assert_eq!(err.kind(), &Kind::ClientAlreadyExists(msg.client_id));
        } else {
            panic!("expected an error");
        }
    }
}

