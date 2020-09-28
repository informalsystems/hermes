use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client_def::{AnyClient, AnyClientState, AnyConsensusState, ClientDef};
use crate::ics02_client::context::{ClientReader, ClientKeeper};
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientEvent, ClientResult};

use crate::ics02_client::msgs::MsgUpdateAnyClient;
use crate::ics02_client::state::ClientState;
use crate::ics24_host::identifier::ClientId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpdateClientResult {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
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
    ctx.consensus_state(&client_id, latest_height)
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
    keeper.store_client_result(ClientResult::UpdateResult(result))
}

#[cfg(test)]
mod tests {
    use tendermint::block::Height;

    use super::*;
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::context_mock::MockClientContext;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::mock_client::header::MockHeader;
    use crate::ics02_client::handler::dispatch;
    use crate::ics02_client::msgs::ClientMsg;

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
    #[test]
    fn test_update_two_chains() {
        let client_ibc1_on_ibc0: ClientId = "ibconeclient".parse().unwrap();
        let client_ibc0_on_ibc1: ClientId = "ibczeroclient".parse().unwrap();
        let signer = get_dummy_account_id();

        let ibc0_start_height = 10;
        let ibc1_start_height = 20;
        let max_history_size = 3;
        let num_iterations = 4;

        let mut ctx_ibc0 = MockClientContext::new(ibc0_start_height, max_history_size);
        let mut ctx_ibc1 = MockClientContext::new(ibc1_start_height, max_history_size);
        ctx_ibc0.with_client(&client_ibc1_on_ibc0, ClientType::Mock, Height(ibc1_start_height));
        ctx_ibc1.with_client(&client_ibc0_on_ibc1, ClientType::Mock, Height(ibc0_start_height));

        ctx_ibc0.chain_context.add_header(ibc0_start_height+1);

        for _i in 0..num_iterations {
            let ibc0_latest_height = ctx_ibc0.chain_context.latest;
            let record_ibc0_on_ibc1 = ctx_ibc1.clients.get(&client_ibc0_on_ibc1).unwrap();
            if record_ibc0_on_ibc1.consensus_states.get(&ibc0_latest_height).is_none() {
                let msg = MsgUpdateAnyClient {
                    client_id: client_ibc0_on_ibc1.clone(),
                    header: MockHeader(Height(u64::from(ibc0_latest_height))).into(),
                    signer,
                };
                let res = dispatch(&mut ctx_ibc1, ClientMsg::UpdateClient(msg.clone()));
                assert_eq!(res.is_ok(), true);
            }
        }
    }
}
