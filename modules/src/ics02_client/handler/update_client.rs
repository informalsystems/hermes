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
    use crate::ics02_client::mocks::*;
    use crate::ics02_client::state::{ClientState, ConsensusState};
    use crate::ics23_commitment::CommitmentRoot;
    use crate::Height;
    use thiserror::Error;

    #[test]
    fn test_update_client_ok() {
        let mock = MockClientReader {
            client_id: "mockclient".parse().unwrap(),
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
        let mock = MockClientReader {
            client_id: "mockclient".parse().unwrap(),
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
        let mock = MockClientReader {
            client_id: "mockclient".parse().unwrap(),
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

