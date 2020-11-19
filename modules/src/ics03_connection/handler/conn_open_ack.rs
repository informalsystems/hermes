//! Protocol logic specific to processing ICS3 messages of type `MsgConnectionOpenAck`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::verify::{check_client_consensus_height, verify_proofs};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenAck;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;

pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenAck,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // Check the client's (consensus state) proof height.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn_end = match ctx.connection_end(msg.connection_id()) {
        // A connection end must exist and must be Init or TryOpen; otherwise we return an error.
        Some(old_conn_end) => {
            // Check if the connection state is either Init or TryOpen and message version
            // is compatible.
            let state_is_consistent = old_conn_end.state_matches(&State::Init)
                && old_conn_end.versions().contains(msg.version())
                || old_conn_end.state_matches(&State::TryOpen)
                    && old_conn_end.versions().get(0).eq(&Some(msg.version()));

            // Check that if the msg's counterparty connection id is not empty then it matches
            // the old connection's counterparty.
            let counterparty_matches = msg.counterparty_connection_id().is_none()
                || old_conn_end.counterparty().connection_id() == msg.counterparty_connection_id();

            if state_is_consistent && counterparty_matches {
                Ok(old_conn_end)
            } else {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(Kind::ConnectionMismatch(
                    msg.connection_id().clone(),
                )))
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
            msg.counterparty_connection_id().cloned(), // This chain's connection id as known on counterparty.
            ctx.commitment_prefix(),                   // Local commitment prefix.
        ),
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

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::handler::EventType;
    use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
    use crate::ics03_connection::context::ConnectionReader;
    use crate::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::ics03_connection::msgs::conn_open_ack::test_util::get_dummy_msg_conn_open_ack;
    use crate::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
    use crate::ics03_connection::msgs::ConnectionMsg;
    use crate::ics23_commitment::commitment::CommitmentPrefix;
    use crate::ics24_host::identifier::{ChainId, ClientId};
    use crate::mock::context::MockContext;
    use crate::mock::host::HostType;
    use crate::Height;

    #[test]
    fn conn_open_ack_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ConnectionMsg,
            want_pass: bool,
        }

        let client_id = ClientId::from_str("mock_clientid").unwrap();
        let msg_ack = MsgConnectionOpenAck::try_from(get_dummy_msg_conn_open_ack()).unwrap();
        let counterparty = Counterparty::new(
            client_id.clone(),
            msg_ack.counterparty_connection_id().cloned(),
            CommitmentPrefix::from(vec![]),
        );

        let incorrect_context = MockContext::default();

        // A connection end (with incorrect state `Open`) that will be part of the context.
        let incorrect_conn_end_state = ConnectionEnd::new(
            State::Open,
            client_id.clone(),
            counterparty,
            incorrect_context.get_compatible_versions(),
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
        incorrect_conn_end_prefix.set_version(msg_ack.version().clone());

        // Build a connection end that will exercise the successful path.
        let correct_counterparty = Counterparty::new(
            client_id.clone(),
            msg_ack.counterparty_connection_id().cloned(),
            CommitmentPrefix::from(b"ibc".to_vec()),
        );
        let correct_conn_end = ConnectionEnd::new(
            State::Init,
            client_id.clone(),
            correct_counterparty,
            vec![msg_ack.version().clone()],
        )
        .unwrap();

        // Parametrize the (correct) host chain to have a height at least as recent as the
        // the height of the proofs in the Ack msg.
        let correct_context = MockContext::new(
            ChainId::new("mockgaia", 1).unwrap(),
            HostType::Mock,
            5,
            Height::new(1, msg_ack.proofs().height().increment().version_height),
        );

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails due to missing connection in context".to_string(),
                ctx: correct_context.clone(),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails due to connections mismatch (incorrect state)".to_string(),
                ctx: correct_context
                    .clone()
                    .with_client(&client_id, Height::new(0, 10))
                    .with_connection(msg_ack.connection_id().clone(), incorrect_conn_end_state),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails due to connections mismatch (incorrect versions)"
                    .to_string(),
                ctx: correct_context
                    .clone()
                    .with_client(&client_id, Height::new(0, 10))
                    .with_connection(msg_ack.connection_id().clone(), incorrect_conn_end_vers),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails: ConsensusStateVerificationFailure due to empty counterparty prefix".to_string(),
                ctx: correct_context
                    .clone()
                    .with_client(&client_id, Height::new(0, 10))
                    .with_connection(msg_ack.connection_id().clone(), incorrect_conn_end_prefix),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails due to MissingLocalConsensusState".to_string(),
                ctx: incorrect_context
                    .with_client(&client_id, Height::new(0, 10))
                    .with_connection(msg_ack.connection_id().clone(), correct_conn_end.clone()),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: false,
            },
            Test {
                name: "Successful processing of Ack message".to_string(),
                ctx: correct_context
                    .with_client(&client_id, Height::new(0, 10))
                    .with_connection(msg_ack.connection_id().clone(), correct_conn_end),
                msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = dispatch(&test.ctx, test.msg.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert_eq!(
                        test.want_pass,
                        true,
                        "conn_open_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have OPEN state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_id, msg_ack.connection_id().clone());
                    assert_eq!(res.connection_end.state().clone(), State::Open);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("connection_open_ack".to_string()));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "conn_open_ack: failed for test: {}, \nparams {:?} {:?} error: {:?}",
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
