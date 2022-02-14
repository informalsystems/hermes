//! Protocol logic specific to processing ICS2 messages of type `MsgCreateAnyClient`.

use crate::prelude::*;

use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::context::ClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::events::Attributes;
use crate::core::ics02_client::handler::ClientResult;
use crate::core::ics02_client::height::Height;
use crate::core::ics02_client::msgs::create_client::MsgCreateAnyClient;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::timestamp::Timestamp;

/// The result following the successful processing of a `MsgCreateAnyClient` message. Preferably
/// this data type should be used with a qualified name `create_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
    pub processed_time: Timestamp,
    pub processed_height: Height,
}

pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgCreateAnyClient,
) -> HandlerResult<ClientResult, Error> {
    let mut output = HandlerOutput::builder();

    // Construct this client's identifier
    let id_counter = ctx.client_counter()?;
    let client_id = ClientId::new(msg.client_state.client_type(), id_counter).map_err(|e| {
        Error::client_identifier_constructor(msg.client_state.client_type(), id_counter, e)
    })?;

    output.log(format!(
        "success: generated new client identifier: {}",
        client_id
    ));

    let result = ClientResult::Create(Result {
        client_id: client_id.clone(),
        client_type: msg.client_state.client_type(),
        client_state: msg.client_state.clone(),
        consensus_state: msg.consensus_state,
        processed_time: ctx.host_timestamp(),
        processed_height: ctx.host_height(),
    });

    let event_attributes = Attributes {
        client_id,
        ..Default::default()
    };
    output.emit(IbcEvent::CreateClient(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use core::time::Duration;
    use test_log::test;

    use crate::clients::ics07_tendermint::client_state::{
        AllowUpdate, ClientState as TendermintClientState,
    };
    use crate::clients::ics07_tendermint::header::test_util::get_dummy_tendermint_header;
    use crate::core::ics02_client::client_consensus::AnyConsensusState;
    use crate::core::ics02_client::client_state::ClientState;
    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics02_client::handler::{dispatch, ClientResult};
    use crate::core::ics02_client::msgs::create_client::MsgCreateAnyClient;
    use crate::core::ics02_client::msgs::ClientMsg;
    use crate::core::ics02_client::trust_threshold::TrustThreshold;
    use crate::core::ics23_commitment::specs::ProofSpecs;
    use crate::core::ics24_host::identifier::ClientId;
    use crate::events::IbcEvent;
    use crate::handler::HandlerOutput;
    use crate::mock::client_state::{MockClientState, MockConsensusState};
    use crate::mock::context::MockContext;
    use crate::mock::header::MockHeader;
    use crate::test_utils::get_dummy_account_id;
    use crate::Height;

    #[test]
    fn test_create_client_ok() {
        let ctx = MockContext::default();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 42);

        let msg = MsgCreateAnyClient::new(
            MockClientState::new(MockHeader::new(height)).into(),
            MockConsensusState::new(MockHeader::new(height)).into(),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result, mut events, ..
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                let expected_client_id = ClientId::new(ClientType::Mock, 0).unwrap();
                assert!(
                    matches!(event, IbcEvent::CreateClient(e) if e.client_id() == &expected_client_id)
                );
                match result {
                    ClientResult::Create(create_result) => {
                        assert_eq!(create_result.client_type, ClientType::Mock);
                        assert_eq!(create_result.client_id, expected_client_id);
                        assert_eq!(create_result.client_state, msg.client_state);
                        assert_eq!(create_result.consensus_state, msg.consensus_state);
                    }
                    _ => {
                        panic!("unexpected result type: expected ClientResult::CreateResult!");
                    }
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_create_client_ok_multiple() {
        let existing_client_id = ClientId::default();
        let signer = get_dummy_account_id();
        let height = Height::new(0, 80);

        let ctx = MockContext::default().with_client(&existing_client_id, height);

        let create_client_msgs: Vec<MsgCreateAnyClient> = vec![
            MsgCreateAnyClient::new(
                MockClientState::new(MockHeader::new(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                MockConsensusState::new(MockHeader::new(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                signer.clone(),
            )
            .unwrap(),
            MsgCreateAnyClient::new(
                MockClientState::new(MockHeader::new(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                MockConsensusState::new(MockHeader::new(Height {
                    revision_height: 42,
                    ..height
                }))
                .into(),
                signer.clone(),
            )
            .unwrap(),
            MsgCreateAnyClient::new(
                MockClientState::new(MockHeader::new(Height {
                    revision_height: 50,
                    ..height
                }))
                .into(),
                MockConsensusState::new(MockHeader::new(Height {
                    revision_height: 50,
                    ..height
                }))
                .into(),
                signer,
            )
            .unwrap(),
        ]
        .into_iter()
        .collect();

        // The expected client id that will be generated will be identical to "9999-mock-0" for all
        // tests. This is because we're not persisting any client results (which is done via the
        // tests for `ics26_routing::dispatch`.
        let expected_client_id = ClientId::new(ClientType::Mock, 0).unwrap();

        for msg in create_client_msgs {
            let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

            match output {
                Ok(HandlerOutput {
                    result, mut events, ..
                }) => {
                    assert_eq!(events.len(), 1);
                    let event = events.pop().unwrap();
                    assert!(
                        matches!(event, IbcEvent::CreateClient(e) if e.client_id() == &expected_client_id)
                    );
                    match result {
                        ClientResult::Create(create_res) => {
                            assert_eq!(create_res.client_type, msg.client_state.client_type());
                            assert_eq!(create_res.client_id, expected_client_id);
                            assert_eq!(create_res.client_state, msg.client_state);
                            assert_eq!(create_res.consensus_state, msg.consensus_state);
                        }
                        _ => {
                            panic!("expected result of type ClientResult::CreateResult");
                        }
                    }
                }
                Err(err) => {
                    panic!("unexpected error: {}", err);
                }
            }
        }
    }

    #[test]
    fn test_tm_create_client_ok() {
        let signer = get_dummy_account_id();

        let ctx = MockContext::default();

        let tm_header = get_dummy_tendermint_header();

        let tm_client_state = TendermintClientState::new(
            tm_header.chain_id.clone().into(),
            TrustThreshold::ONE_THIRD,
            Duration::from_secs(64000),
            Duration::from_secs(128000),
            Duration::from_millis(3000),
            Height::new(0, u64::from(tm_header.height)),
            ProofSpecs::default(),
            vec!["".to_string()],
            AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        )
        .unwrap()
        .wrap_any();

        let msg = MsgCreateAnyClient::new(
            tm_client_state,
            AnyConsensusState::Tendermint(tm_header.try_into().unwrap()),
            signer,
        )
        .unwrap();

        let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result, mut events, ..
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                let expected_client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
                assert!(
                    matches!(event, IbcEvent::CreateClient(e) if e.client_id() == &expected_client_id)
                );
                match result {
                    ClientResult::Create(create_res) => {
                        assert_eq!(create_res.client_type, ClientType::Tendermint);
                        assert_eq!(create_res.client_id, expected_client_id);
                        assert_eq!(create_res.client_state, msg.client_state);
                        assert_eq!(create_res.consensus_state, msg.consensus_state);
                    }
                    _ => {
                        panic!("expected result of type ClientResult::CreateResult");
                    }
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }
}
