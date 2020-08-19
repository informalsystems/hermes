#![allow(unreachable_code, unused_variables)]

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClient, ClientDef};
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientEvent, ClientKeeper, ClientReader};
use crate::ics02_client::msgs::MsgUpdateAnyClient;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics24_host::identifier::ClientId;

#[derive(Debug)]
pub struct UpdateClientResult<CD: ClientDef> {
    client_id: ClientId,
    client_state: CD::ClientState,
    consensus_state: CD::ConsensusState,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgUpdateAnyClient<AnyClient>,
) -> HandlerResult<UpdateClientResult<AnyClient>, Error> {
    let mut output = HandlerOutput::builder();

    let MsgUpdateAnyClient { client_id, header } = msg;

    let client_type = ctx
        .client_type(&client_id)
        .ok_or_else(|| Kind::ClientNotFound(client_id.clone()))?;

    let client_state = ctx
        .client_state(&client_id)
        .ok_or_else(|| Kind::ClientNotFound(client_id.clone()))?;

    let latest_height = client_state.get_latest_height();
    let consensus_state = ctx
        .consensus_state(&client_id, latest_height)
        .ok_or_else(|| Kind::ConsensusStateNotFound(client_id.clone(), latest_height))?;

    // Use client_state to validate the new header against the latest consensus_state.
    // This function will return the new client_state (its latest_height changed) and a
    // consensus_state obtained from header. These will be later persisted by the keeper.
    // FIXME
    // (new_client_state, new_consensus_state) =
    //    CD::check_validity_and_update_state(client_state, consensus_state, &header)?;

    output.emit(ClientEvent::ClientUpdated(client_id.clone()));

    Ok(output.with_result(UpdateClientResult {
        client_id,
        client_state,    // new_client_state
        consensus_state, // new_consensus_state
    }))
}

pub fn keep(
    keeper: &mut dyn ClientKeeper,
    result: UpdateClientResult<AnyClient>,
) -> Result<(), Error> {
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
            client_type: Some(ClientType::Tendermint),
            client_state: MockClientState(42).into(),
            consensus_state: MockConsensusState(42).into(),
        };

        let msg = MsgUpdateAnyClient {
            client_id: "mockclient".parse().unwrap(),
            header: MockHeader(46).into(),
        };

        let output = process(&mock, msg.clone());

        match output {
            Ok(HandlerOutput {
                result: _,
                events,
                log,
            }) => {
                // assert_eq!(result.client_state, MockClientState(0));
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
}
