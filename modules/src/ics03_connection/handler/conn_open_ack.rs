use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::verify::{check_client_consensus_height, verify_proofs};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenAck;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::MsgConnectionOpenAck;

/// Protocol logic specific to processing ICS3 messages of type `MsgConnectionOpenAck`.
pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenAck,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // Check the client's (consensus state) proof height.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn_end = match ctx.fetch_connection_end(msg.connection_id()) {
        // A connection end must exist and must be Init or TryOpen; otherwise we return an error.
        Some(old_conn_end) => {
            if !((old_conn_end.state_matches(&State::Init)
                && old_conn_end.versions().contains(msg.version()))
                || (old_conn_end.state_matches(&State::TryOpen)
                    && old_conn_end.versions().get(0).eq(&Some(msg.version()))))
            {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(Kind::ConnectionMismatch(
                    msg.connection_id().clone(),
                )))
            } else {
                Ok(old_conn_end.clone())
            }
        }
        None => {
            // No connection end exists for this conn. identifier. Impossible to continue handshake.
            Err(Into::<Error>::into(Kind::UninitializedConnection(
                msg.connection_id().clone(),
            )))
        }
    }?;

    // Proof verification.
    let expected_conn = ConnectionEnd::new(
        State::TryOpen,
        new_conn_end.counterparty().client_id().clone(),
        Counterparty::new(
            // The counterparty is the local chain.
            new_conn_end.client_id().clone(), // The local client identifier.
            msg.connection_id().clone(),      // Local connection id.
            ctx.commitment_prefix(),          // Local commitment prefix.
        )?,
        vec![msg.version().clone()],
    )?;
    // 2. Pass the details to the verification function.
    verify_proofs(
        ctx,
        msg.connection_id(),
        msg.client_state(),
        &new_conn_end,
        &expected_conn,
        msg.proofs(),
    )?;

    output.log("success: connection verification passed");

    new_conn_end.set_state(State::Open);
    new_conn_end.set_version(msg.version().clone());

    let result = ConnectionResult {
        connection_end: new_conn_end,
        connection_id: msg.connection_id().clone(),
    };

    output.emit(ConnOpenAck(result.clone()));

    Ok(output.with_result(result))
}

pub fn keep(keeper: &mut dyn ConnectionKeeper, result: ConnectionResult) -> Result<(), Error> {
    keeper.store_connection(&result.connection_id, &result.connection_end)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::handler::EventType;
    use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
    use crate::ics03_connection::context::ConnectionReader;
    use crate::ics03_connection::context_mock::MockConnectionContext;
    use crate::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::ics03_connection::msgs::test_util::get_dummy_msg_conn_open_ack;
    use crate::ics03_connection::msgs::{ConnectionMsg, MsgConnectionOpenAck};
    use crate::ics23_commitment::commitment::CommitmentPrefix;
    use crate::ics24_host::identifier::ClientId;
    use crate::try_from_raw::TryFromRaw;
    use std::str::FromStr;

    #[test]
    fn conn_open_ack_msg_processing() {
        #[derive(Clone, Debug)]
        struct ConnOpenAckProcessParams {
            ctx: MockConnectionContext,
            msg: ConnectionMsg,
        }

        struct Test {
            name: String,
            ctx: MockConnectionContext,
            msg: ConnectionMsg,
            want_pass: bool,
        }

        let client_id = ClientId::from_str("mock_clientid").unwrap();
        let dummy_msg = MsgConnectionOpenAck::try_from(get_dummy_msg_conn_open_ack()).unwrap();
        let counterparty = Counterparty::new(
            client_id.clone(),
            dummy_msg.connection_id().clone(),
            CommitmentPrefix::from(vec![]),
        )
        .unwrap();
        let default_context = MockConnectionContext::new(10, 3);

        // A connection end (with incorrect state `Open`) that will be part of the context.
        let incorrect_conn_end_state = ConnectionEnd::new(
            State::Open,
            client_id.clone(),
            counterparty,
            default_context.get_compatible_versions(),
        )
        .unwrap();

        // A connection end (with correct state but incorrect versions); exercises unsuccessful
        // processing path.
        let mut incorrect_conn_end_vers = incorrect_conn_end_state.clone();
        incorrect_conn_end_vers.set_state(State::Init);

        // A connection end (with correct versions and correct state, but incorrect prefix for the
        // counterparty) that will be part of the context to exercise unsuccessful path.
        let mut incorrect_conn_end_prefix = incorrect_conn_end_state.clone();
        incorrect_conn_end_prefix.set_state(State::Init);
        incorrect_conn_end_prefix.set_version(dummy_msg.version().clone());

        // Build a connection end that will exercise the successful path.
        let correct_counterparty = Counterparty::new(
            client_id.clone(),
            dummy_msg.connection_id().clone(),
            CommitmentPrefix::from(b"ibc".to_vec()),
        )
        .unwrap();
        let correct_conn_end = ConnectionEnd::new(
            State::Init,
            client_id.clone(),
            correct_counterparty,
            vec![dummy_msg.version().clone()],
        )
        .unwrap();

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails due to missing connection in context".to_string(),
                ctx: default_context.clone(),
                msg: ConnectionMsg::ConnectionOpenAck(dummy_msg.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails due to connections mismatch (incorrect state)".to_string(),
                ctx: default_context
                    .clone()
                    .with_client_state(&client_id, 10)
                    .add_connection(dummy_msg.connection_id().clone(), incorrect_conn_end_state),
                msg: ConnectionMsg::ConnectionOpenAck(dummy_msg.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails due to connections mismatch (incorrect versions)"
                    .to_string(),
                ctx: default_context
                    .clone()
                    .with_client_state(&client_id, 10)
                    .add_connection(dummy_msg.connection_id().clone(), incorrect_conn_end_vers),
                msg: ConnectionMsg::ConnectionOpenAck(dummy_msg.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails: ConsensusStateVerificationFailure due to empty counterparty prefix".to_string(),
                ctx: default_context
                    .clone()
                    .with_client_state(&client_id, 10)
                    .add_connection(dummy_msg.connection_id().clone(), incorrect_conn_end_prefix),
                msg: ConnectionMsg::ConnectionOpenAck(dummy_msg.clone()),
                want_pass: false,
            },
            Test {
                name: "Successful processing of Ack message".to_string(),
                ctx: default_context
                    .with_client_state(&client_id, 10)
                    .add_connection(dummy_msg.connection_id().clone(), correct_conn_end),
                msg: ConnectionMsg::ConnectionOpenAck(dummy_msg.clone()),
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for mut test in tests {
            let res = dispatch(&mut test.ctx, test.msg.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert_eq!(
                        test.want_pass,
                        true,
                        "process_ics3_msg() test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have OPEN state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_id, dummy_msg.connection_id().clone());
                    assert_eq!(res.connection_end.state().clone(), State::Open);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("connection_open_ack".to_string()));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "process_ics3_msg() failed for test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.msg,
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}
