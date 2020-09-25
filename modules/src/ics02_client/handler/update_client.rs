#![allow(unreachable_code, unused_variables)]

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClient, AnyClientState, AnyConsensusState, ClientDef};
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::ClientEvent;

use crate::ics02_client::msgs::MsgUpdateAnyClient;
use crate::ics02_client::state::ClientState;
use crate::ics24_host::identifier::ClientId;

#[derive(Debug)]
pub struct UpdateClientResult {
    client_id: ClientId,
    client_state: AnyClientState,
    consensus_state: AnyConsensusState,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgUpdateAnyClient,
) -> HandlerResult<UpdateClientResult, Error> {
    let mut output = HandlerOutput::builder();

    let MsgUpdateAnyClient {
        client_id,
        header,
        signer: _,
    } = msg;

    let client_type = ctx
        .client_type(&client_id)
        .ok_or_else(|| Kind::ClientNotFound(client_id.clone()))?;

    let client_def = AnyClient::from_client_type(client_type);

    let client_state = ctx
        .client_state(&client_id)
        .ok_or_else(|| Kind::ClientNotFound(client_id.clone()))?;

    let latest_height = client_state.latest_height();
    let consensus_state = ctx
        .consensus_state(&client_id, latest_height)
        .ok_or_else(|| Kind::ConsensusStateNotFound(client_id.clone(), latest_height))?;

    // Use client_state to validate the new header against the latest consensus_state.
    // This function will return the new client_state (its latest_height changed) and a
    // consensus_state obtained from header. These will be later persisted by the keeper.
    let (new_client_state, new_consensus_state) = client_def
        .check_header_and_update_state(client_state, header)
        .map_err(|_| Kind::HeaderVerificationFailure)?;

    output.emit(ClientEvent::ClientUpdated(client_id.clone()));

    Ok(output.with_result(UpdateClientResult {
        client_id,
        client_state: new_client_state,
        consensus_state: new_consensus_state,
    }))
}

pub fn keep(keeper: &mut dyn ClientKeeper, result: UpdateClientResult) -> Result<(), Error> {
    keeper.store_client_state(result.client_id.clone(), result.client_state)?;
    keeper.store_consensus_state(result.client_id, result.consensus_state)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use tendermint::block::Height;

    use super::*;
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::context_mock::MockClientContext;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::mock_client::header::MockHeader;

    #[test]
    fn test_update_client_ok() {
        let client_id: ClientId = "mockclient".parse().unwrap();
        let signer = get_dummy_account_id();

        let mut ctx = MockClientContext::default();
        ctx.with_client(&client_id, ClientType::Mock, Height(42));

        let msg = MsgUpdateAnyClient {
            client_id,
            header: MockHeader(Height(46)).into(),
            signer,
        };

        let output = process(&ctx, msg.clone());

        match output {
            Ok(HandlerOutput {
                result: _,
                events,
                log,
            }) => {
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
    fn test_update_nonexisting_client() {
        let client_id: ClientId = "mockclient1".parse().unwrap();
        let signer = get_dummy_account_id();

        let mut ctx = MockClientContext::default();
        ctx.with_client_consensus_state(&client_id, Height(42));

        let msg = MsgUpdateAnyClient {
            client_id: "nonexistingclient".parse().unwrap(),
            header: MockHeader(Height(46)).into(),
            signer,
        };

        let output = process(&ctx, msg.clone());

        match output {
            Ok(_) => {
                panic!("unexpected success (expected error)");
            }
            Err(err) => {
                assert_eq!(err.kind(), &Kind::ClientNotFound(msg.client_id));
            }
        }
    }

    #[test]
    fn test_update_client_ok_multiple() {
        let client_ids: Vec<ClientId> = vec![
            "mockclient1".parse().unwrap(),
            "mockclient2".parse().unwrap(),
            "mockclient3".parse().unwrap(),
        ];
        let signer = get_dummy_account_id();

        let initial_height = Height(45);
        let update_height = Height(49);

        let mut ctx = MockClientContext::default();

        for cid in &client_ids {
            ctx.with_client_consensus_state(cid, initial_height);
        }

        for cid in &client_ids {
            let msg = MsgUpdateAnyClient {
                client_id: cid.clone(),
                header: MockHeader(update_height).into(),
                signer,
            };

            let output = process(&ctx, msg.clone());

            match output {
                Ok(HandlerOutput {
                    result: _,
                    events,
                    log,
                }) => {
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
}
