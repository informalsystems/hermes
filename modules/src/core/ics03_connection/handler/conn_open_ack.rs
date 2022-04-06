//! Protocol logic specific to processing ICS3 messages of type `MsgConnectionOpenAck`.

use crate::core::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use crate::core::ics03_connection::context::ConnectionReader;
use crate::core::ics03_connection::error::Error;
use crate::core::ics03_connection::events::Attributes;
use crate::core::ics03_connection::handler::verify::{
    check_client_consensus_height, verify_proofs,
};
use crate::core::ics03_connection::handler::{ConnectionIdState, ConnectionResult};
use crate::core::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;

pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenAck,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // Check the client's (consensus state) proof height.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Validate the connection end.
    let mut conn_end = ctx.connection_end(&msg.connection_id)?;
    // A connection end must be Init or TryOpen; otherwise we return an error.
    let state_is_consistent = conn_end.state_matches(&State::Init)
        && conn_end.versions().contains(&msg.version)
        || conn_end.state_matches(&State::TryOpen)
            && conn_end.versions().get(0).eq(&Some(&msg.version));

    if !state_is_consistent {
        // Old connection end is in incorrect state, propagate the error.
        return Err(Error::connection_mismatch(msg.connection_id));
    }

    // Set the connection ID of the counterparty
    let prev_counterparty = conn_end.counterparty();
    let counterparty = Counterparty::new(
        prev_counterparty.client_id().clone(),
        Some(msg.connection_id.clone()),
        prev_counterparty.prefix().clone(),
    );
    conn_end.set_state(State::Open);
    conn_end.set_version(msg.version.clone());
    conn_end.set_counterparty(counterparty);

    // The counterparty is the local chain.
    let counterparty = Counterparty::new(
        conn_end.client_id().clone(), // The local client identifier.
        Some(msg.counterparty_connection_id.clone()), // This chain's connection id as known on counterparty.
        ctx.commitment_prefix(),                      // Local commitment prefix.
    );

    // Proof verification.
    let expected_conn = ConnectionEnd::new(
        State::TryOpen,
        conn_end.counterparty().client_id().clone(),
        counterparty,
        vec![msg.version.clone()],
        conn_end.delay_period(),
    );

    // 2. Pass the details to the verification function.
    verify_proofs(
        ctx,
        msg.client_state.clone(),
        msg.proofs.height(),
        &conn_end,
        &expected_conn,
        &msg.proofs,
    )?;

    output.log("success: connection verification passed");

    let result = ConnectionResult {
        connection_id: msg.connection_id,
        connection_id_state: ConnectionIdState::Reused,
        connection_end: conn_end,
    };

    let event_attributes = Attributes {
        connection_id: Some(result.connection_id.clone()),
        height: ctx.host_current_height(),
        ..Default::default()
    };
    output.emit(IbcEvent::OpenAckConnection(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use core::str::FromStr;
    use test_log::test;

    use crate::core::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
    use crate::core::ics03_connection::context::ConnectionReader;
    use crate::core::ics03_connection::error;
    use crate::core::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::core::ics03_connection::msgs::conn_open_ack::test_util::get_dummy_raw_msg_conn_open_ack;
    use crate::core::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
    use crate::core::ics03_connection::msgs::ConnectionMsg;
    use crate::core::ics23_commitment::commitment::CommitmentPrefix;
    use crate::core::ics24_host::identifier::{ChainId, ClientId};
    use crate::events::IbcEvent;
    use crate::mock::context::MockContext;
    use crate::mock::host::HostType;
    use crate::timestamp::ZERO_DURATION;

    #[test]
    fn conn_open_ack_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ConnectionMsg,
            want_pass: bool,
            match_error: Box<dyn FnOnce(error::Error)>,
        }

        let msg_ack =
            MsgConnectionOpenAck::try_from(get_dummy_raw_msg_conn_open_ack(10, 10)).unwrap();
        let conn_id = msg_ack.connection_id.clone();

        // Client parameters -- identifier and correct height (matching the proof height)
        let client_id = ClientId::from_str("mock_clientid").unwrap();
        let proof_height = msg_ack.proofs.height();

        // Parametrize the host chain to have a height at least as recent as the
        // the height of the proofs in the Ack msg.
        let latest_height = proof_height.increment();
        let max_history_size = 5;
        let default_context = MockContext::new(
            ChainId::new("mockgaia".to_string(), latest_height.revision_number),
            HostType::Mock,
            max_history_size,
            latest_height,
        );

        // A connection end that will exercise the successful path.
        let default_conn_end = ConnectionEnd::new(
            State::Init,
            client_id.clone(),
            Counterparty::new(
                client_id.clone(),
                Some(msg_ack.counterparty_connection_id.clone()),
                CommitmentPrefix::try_from(b"ibc".to_vec()).unwrap(),
            ),
            vec![msg_ack.version.clone()],
            ZERO_DURATION,
        );

        // A connection end with incorrect state `Open`; will be part of the context.
        let mut conn_end_open = default_conn_end.clone();
        conn_end_open.set_state(State::Open); // incorrect field

        let tests: Vec<Test> = vec![
            Test {
                name: "Successful processing of an Ack message".to_string(),
                ctx: default_context
                    .clone()
                    .with_client(&client_id, proof_height)
                    .with_connection(conn_id.clone(), default_conn_end),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: true,
                match_error: Box::new(|_| panic!("should not have error")),
            },
            Test {
                name: "Processing fails because the connection does not exist in the context"
                    .to_string(),
                ctx: default_context.clone(),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: false,
                match_error: {
                    let connection_id = conn_id.clone();
                    Box::new(move |e| match e.detail() {
                        error::ErrorDetail::ConnectionNotFound(e) => {
                            assert_eq!(e.connection_id, connection_id)
                        }
                        _ => {
                            panic!("Expected ConnectionNotFound error");
                        }
                    })
                },
            },
            Test {
                name: "Processing fails due to connections mismatch (incorrect 'open' state)"
                    .to_string(),
                ctx: default_context
                    .with_client(&client_id, proof_height)
                    .with_connection(conn_id.clone(), conn_end_open),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack)),
                want_pass: false,
                match_error: {
                    let connection_id = conn_id;
                    Box::new(move |e| match e.detail() {
                        error::ErrorDetail::ConnectionMismatch(e) => {
                            assert_eq!(e.connection_id, connection_id);
                        }
                        _ => {
                            panic!("Expected ConnectionMismatch error");
                        }
                    })
                },
            },
            /*
            Test {
                name: "Processing fails due to MissingLocalConsensusState".to_string(),
                ctx: MockContext::default()
                    .with_client(&client_id, proof_height)
                    .with_connection(conn_id, default_conn_end),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack)),
                want_pass: false,
                error_kind: Some(Kind::MissingLocalConsensusState)
            },
            */
        ];

        for test in tests {
            let res = dispatch(&test.ctx, test.msg.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert!(
                        test.want_pass,
                        "conn_open_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );

                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have OPEN state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_end.state().clone(), State::Open);

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::OpenAckConnection(_)));
                        assert_eq!(e.height(), test.ctx.host_current_height());
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "conn_open_ack: failed for test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.msg,
                        test.ctx.clone(),
                        e,
                    );

                    // Verify that the error kind matches
                    (test.match_error)(e);
                }
            }
        }
    }
}
