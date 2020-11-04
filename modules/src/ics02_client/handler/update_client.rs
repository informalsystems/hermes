//! Protocol logic specific to processing ICS2 messages of type `MsgUpdateAnyClient`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClient, AnyClientState, AnyConsensusState, ClientDef};
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientEvent, ClientResult};

use crate::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use crate::ics24_host::identifier::ClientId;

/// The result following the successful processing of a `MsgUpdateAnyClient` message. Preferably
/// this data type should be used with a qualified name `update_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgUpdateAnyClient,
) -> HandlerResult<ClientResult, Error> {
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
    ctx.consensus_state(&client_id, latest_height)
        .ok_or_else(|| Kind::ConsensusStateNotFound(client_id.clone(), latest_height))?;

    // Use client_state to validate the new header against the latest consensus_state.
    // This function will return the new client_state (its latest_height changed) and a
    // consensus_state obtained from header. These will be later persisted by the keeper.
    let (new_client_state, new_consensus_state) = client_def
        .check_header_and_update_state(client_state, header)
        .map_err(|e| Kind::HeaderVerificationFailure.context(e.to_string()))?;

    output.emit(ClientEvent::ClientUpdated(client_id.clone()));

    Ok(output.with_result(ClientResult::Update(Result {
        client_id,
        client_state: new_client_state,
        consensus_state: new_consensus_state,
    })))
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::handler::HandlerOutput;
    use crate::ics02_client::client_def::AnyClientState;
    use crate::ics02_client::error::Kind;
    use crate::ics02_client::handler::ClientResult::{Create, Update};
    use crate::ics02_client::handler::{dispatch, ClientEvent};
    use crate::ics02_client::header::Header;
    use crate::ics02_client::msgs::update_client::MsgUpdateAnyClient;
    use crate::ics02_client::msgs::ClientMsg;
    use crate::ics24_host::identifier::ClientId;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::MockClientState;
    use crate::mock_context::MockContext;
    use crate::test_utils::get_dummy_account_id;
    use crate::Height;

    #[test]
    fn test_update_client_ok() {
        let client_id = ClientId::from_str("mockclient").unwrap();
        let signer = get_dummy_account_id();

        let ctx = MockContext::default().with_client(&client_id, Height::new(0, 42));

        let msg = MsgUpdateAnyClient {
            client_id: client_id.clone(),
            header: MockHeader(Height::new(0, 46)).into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                events,
                log,
            }) => {
                assert_eq!(
                    events,
                    vec![ClientEvent::ClientUpdated(msg.client_id).into()]
                );
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert_eq!(
                            upd_res.client_state,
                            AnyClientState::Mock(MockClientState(MockHeader(msg.header.height())))
                        )
                    }
                    Create(_) => panic!("update handler result has type CreateResult"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_nonexisting_client() {
        let client_id = ClientId::from_str("mockclient1").unwrap();
        let signer = get_dummy_account_id();

        let ctx = MockContext::default().with_client(&client_id, Height::new(0, 42));

        let msg = MsgUpdateAnyClient {
            client_id: ClientId::from_str("nonexistingclient").unwrap(),
            header: MockHeader(Height::new(0, 46)).into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

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
        let client_ids = vec![
            ClientId::from_str("mockclient1").unwrap(),
            ClientId::from_str("mockclient2").unwrap(),
            ClientId::from_str("mockclient3").unwrap(),
        ];
        let signer = get_dummy_account_id();
        let initial_height = Height::new(0, 45);
        let update_height = Height::new(0, 49);

        let mut ctx = MockContext::default();

        for cid in &client_ids {
            ctx = ctx.with_client(cid, initial_height);
        }

        for cid in &client_ids {
            let msg = MsgUpdateAnyClient {
                client_id: cid.clone(),
                header: MockHeader(update_height).into(),
                signer,
            };

            let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

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
