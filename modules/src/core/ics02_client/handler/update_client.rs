//! Protocol logic specific to processing ICS2 messages of type `MsgUpdateAnyClient`.

use tracing::debug;

use crate::core::ics02_client::client_state::{ClientState, UpdatedState};
use crate::core::ics02_client::consensus_state::ConsensusState;
use crate::core::ics02_client::context::ClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::events::Attributes;
use crate::core::ics02_client::handler::ClientResult;
use crate::core::ics02_client::height::Height;
use crate::core::ics02_client::msgs::update_client::MsgUpdateClient;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;
use crate::timestamp::Timestamp;

/// The result following the successful processing of a `MsgUpdateAnyClient` message. Preferably
/// this data type should be used with a qualified name `update_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq)]
pub struct Result {
    pub client_id: ClientId,
    pub client_state: Box<dyn ClientState>,
    pub consensus_state: Box<dyn ConsensusState>,
    pub processed_time: Timestamp,
    pub processed_height: Height,
}

pub fn process<Ctx: ClientReader>(
    ctx: &Ctx,
    msg: MsgUpdateClient,
) -> HandlerResult<ClientResult, Error> {
    let mut output = HandlerOutput::builder();

    let MsgUpdateClient {
        client_id,
        header,
        signer: _,
    } = msg;

    // Read client type from the host chain store. The client should already exist.
    // Read client state from the host chain store.
    let client_state = ctx.client_state(&client_id)?;

    if client_state.is_frozen() {
        return Err(Error::client_frozen(client_id));
    }

    // Read consensus state from the host chain store.
    let latest_consensus_state =
        ClientReader::consensus_state(ctx, &client_id, client_state.latest_height()).map_err(
            |_| Error::consensus_state_not_found(client_id.clone(), client_state.latest_height()),
        )?;

    debug!("latest consensus state: {:?}", latest_consensus_state);

    let now = ClientReader::host_timestamp(ctx);
    let duration = now
        .duration_since(&latest_consensus_state.timestamp())
        .ok_or_else(|| {
            Error::invalid_consensus_state_timestamp(latest_consensus_state.timestamp(), now)
        })?;

    if client_state.expired(duration) {
        return Err(Error::header_not_within_trust_period(
            latest_consensus_state.timestamp(),
            now,
        ));
    }

    // Use client_state to validate the new header against the latest consensus_state.
    // This function will return the new client_state (its latest_height changed) and a
    // consensus_state obtained from header. These will be later persisted by the keeper.
    let UpdatedState {
        client_state,
        consensus_state,
    } = client_state
        .check_header_and_update_state(ctx, client_id.clone(), header)
        .map_err(|e| Error::header_verification_failure(e.to_string()))?;

    let result = ClientResult::Update(Result {
        client_id: client_id.clone(),
        client_state,
        consensus_state,
        processed_time: ClientReader::host_timestamp(ctx),
        processed_height: ctx.host_height(),
    });

    let event_attributes = Attributes {
        client_id,
        ..Default::default()
    };
    output.emit(IbcEvent::UpdateClient(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;
    use test_log::test;

    use crate::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
    use crate::core::ics02_client::client_state::ClientState;
    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics02_client::consensus_state::downcast_consensus_state;
    use crate::core::ics02_client::error::{Error, ErrorDetail};
    use crate::core::ics02_client::handler::dispatch;
    use crate::core::ics02_client::handler::ClientResult::Update;
    use crate::core::ics02_client::msgs::update_client::MsgUpdateClient;
    use crate::core::ics02_client::msgs::ClientMsg;
    use crate::core::ics24_host::identifier::{ChainId, ClientId};
    use crate::events::IbcEvent;
    use crate::handler::HandlerOutput;
    use crate::mock::client_state::MockClientState;
    use crate::mock::context::MockContext;
    use crate::mock::header::MockHeader;
    use crate::mock::host::{HostBlock, HostType};
    use crate::prelude::*;
    use crate::test_utils::get_dummy_account_id;
    use crate::timestamp::Timestamp;
    use crate::Height;

    #[test]
    fn test_update_client_ok() {
        let client_id = ClientId::default();
        let signer = get_dummy_account_id();

        let timestamp = Timestamp::now();

        let ctx = MockContext::default().with_client(&client_id, Height::new(0, 42).unwrap());
        let height = Height::new(0, 46).unwrap();
        let msg = MsgUpdateClient {
            client_id: client_id.clone(),
            header: MockHeader::new(height).with_timestamp(timestamp).into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert_eq!(
                            upd_res.client_state,
                            MockClientState::new(MockHeader::new(height).with_timestamp(timestamp))
                                .into_box()
                        )
                    }
                    _ => panic!("update handler result has incorrect type"),
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

        let ctx = MockContext::default().with_client(&client_id, Height::new(0, 42).unwrap());

        let msg = MsgUpdateClient {
            client_id: ClientId::from_str("nonexistingclient").unwrap(),
            header: MockHeader::new(Height::new(0, 46).unwrap()).into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Err(Error(ErrorDetail::ClientNotFound(e), _)) => {
                assert_eq!(e.client_id, msg.client_id);
            }
            _ => {
                panic!("expected ClientNotFound error, instead got {:?}", output)
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
        let initial_height = Height::new(0, 45).unwrap();
        let update_height = Height::new(0, 49).unwrap();

        let mut ctx = MockContext::default();

        for cid in &client_ids {
            ctx = ctx.with_client(cid, initial_height);
        }

        for cid in &client_ids {
            let msg = MsgUpdateClient {
                client_id: cid.clone(),
                header: MockHeader::new(update_height).into(),
                signer: signer.clone(),
            };

            let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

            match output {
                Ok(HandlerOutput {
                    result: _,
                    mut events,
                    log,
                }) => {
                    assert_eq!(events.len(), 1);
                    let event = events.pop().unwrap();
                    assert!(
                        matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
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
    fn test_update_synthetic_tendermint_client_adjacent_ok() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20).unwrap();
        let update_height = Height::new(1, 21).unwrap();

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            Height::new(1, 1).unwrap(),
        )
        .with_client_parametrized(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            update_height,
        );

        let signer = get_dummy_account_id();

        let mut block = ctx_b.host_block(update_height).unwrap().clone();
        block.set_trusted_height(client_height);

        let latest_header_height = block.height();
        let msg = MsgUpdateClient {
            client_id: client_id.clone(),
            header: block.into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert!(!upd_res.client_state.is_frozen());
                        assert_eq!(upd_res.client_state.latest_height(), latest_header_height,)
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_non_adjacent_ok() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20).unwrap();
        let update_height = Height::new(1, 21).unwrap();

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            Height::new(1, 1).unwrap(),
        )
        .with_client_parametrized_history(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            update_height,
        );

        let signer = get_dummy_account_id();

        let mut block = ctx_b.host_block(update_height).unwrap().clone();
        let trusted_height = client_height.clone().sub(1).unwrap();
        block.set_trusted_height(trusted_height);

        let latest_header_height = block.height();
        let msg = MsgUpdateClient {
            client_id: client_id.clone(),
            header: block.into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert!(!upd_res.client_state.is_frozen());
                        assert_eq!(upd_res.client_state.latest_height(), latest_header_height,)
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_duplicate_ok() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20).unwrap();

        let chain_start_height = Height::new(1, 11).unwrap();

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            chain_start_height,
        )
        .with_client_parametrized(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            client_height,
        );

        let signer = get_dummy_account_id();

        let block = ctx_b.host_block(client_height).unwrap().clone();
        let block = match block {
            HostBlock::SyntheticTendermint(mut theader) => {
                let cons_state = ctx.latest_consensus_states(&client_id, &client_height);
                if let Some(tcs) = downcast_consensus_state::<TmConsensusState>(cons_state.as_ref())
                {
                    theader.light_block.signed_header.header.time = tcs.timestamp;
                    theader.trusted_height = Height::new(1, 11).unwrap();
                }
                HostBlock::SyntheticTendermint(theader)
            }
            _ => block,
        };

        let latest_header_height = block.height();
        let msg = MsgUpdateClient {
            client_id: client_id.clone(),
            header: block.into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert!(!upd_res.client_state.is_frozen());
                        assert_eq!(upd_res.client_state, ctx.latest_client_states(&client_id));
                        assert_eq!(upd_res.client_state.latest_height(), latest_header_height,)
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {:?}", err);
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_lower_height() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20).unwrap();

        let client_update_height = Height::new(1, 19).unwrap();

        let chain_start_height = Height::new(1, 11).unwrap();

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            chain_start_height,
        )
        .with_client_parametrized(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            client_height,
        );

        let signer = get_dummy_account_id();

        let block_ref = ctx_b.host_block(client_update_height).unwrap();

        let msg = MsgUpdateClient {
            client_id,
            header: block_ref.clone().into(),
            signer,
        };

        let output = dispatch(&ctx, ClientMsg::UpdateClient(msg));

        match output {
            Ok(_) => {
                panic!("update handler result has incorrect type");
            }
            Err(err) => match err.detail() {
                ErrorDetail::HeaderVerificationFailure(_) => {}
                _ => panic!("unexpected error: {:?}", err),
            },
        }
    }
}
