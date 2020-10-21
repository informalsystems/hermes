//! Protocol logic specific to processing ICS3 messages of type `MsgConnectionOpenTry`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::verify::{check_client_consensus_height, verify_proofs};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenTry;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;

pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenTry,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // Check that consensus height (for client proof) in message is not too advanced nor too old.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end (if any) and validate it against the message.
    let mut new_connection_end = match ctx.connection_end(msg.connection_id()) {
        Some(old_conn_end) => {
            // TODO - change validation to take into account the new `counterparty_chosen_connection_id`
            // Validate that existing connection end matches with the one we're trying to establish.
            if old_conn_end.state_matches(&State::Init)
                && old_conn_end.counterparty_matches(&msg.counterparty())
                && old_conn_end.client_id_matches(msg.client_id())
            {
                // A ConnectionEnd already exists and all validation passed.
                Ok(old_conn_end.clone())
            } else {
                // A ConnectionEnd already exists and validation failed.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch(msg.connection_id().clone())
                        .context(old_conn_end.client_id().to_string()),
                ))
            }
        }
        // No ConnectionEnd exists for this ConnectionId. Create & return a new one.
        None => Ok(ConnectionEnd::new(
            State::Init,
            msg.client_id().clone(),
            msg.counterparty(),
            msg.counterparty_versions(),
        )?),
    }?;

    // Proof verification in two steps:
    // 1. Setup: build the ConnectionEnd as we expect to find it on the other party.
    let expected_conn = ConnectionEnd::new(
        State::Init,
        msg.counterparty().client_id().clone(),
        Counterparty::new(
            msg.client_id().clone(),
            msg.connection_id().clone(),
            ctx.commitment_prefix(),
        )?,
        msg.counterparty_versions(),
    )?;

    // 2. Pass the details to the verification function.
    verify_proofs(
        ctx,
        msg.connection_id(),
        msg.client_state(),
        &new_connection_end,
        &expected_conn,
        msg.proofs(),
    )?;

    // Transition the connection end to the new state & pick a version.
    new_connection_end.set_state(State::TryOpen);

    // Pick the version.
    let local_versions = ctx.get_compatible_versions();
    let intersection: Vec<String> = msg
        .counterparty_versions()
        .iter()
        .filter(|cv| local_versions.contains(cv))
        .cloned()
        .collect();
    new_connection_end.set_version(ctx.pick_version(intersection));

    output.log("success: connection verification passed");

    let result = ConnectionResult {
        connection_id: msg.connection_id().clone(),
        connection_end: new_connection_end,
    };

    output.emit(ConnOpenTry(result.clone()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use crate::handler::EventType;
    use crate::ics03_connection::connection::{ConnectionEnd, State};
    use crate::ics03_connection::context::ConnectionReader;
    use crate::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::ics03_connection::msgs::conn_open_try::test_util::get_dummy_msg_conn_open_try;
    use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
    use crate::ics03_connection::msgs::ConnectionMsg;
    use crate::mock_context::MockContext;
    use crate::Height;

    #[test]
    fn conn_open_try_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ConnectionMsg,
            want_pass: bool,
        }

        let host_chain_height = Height::new(1, 35);
        let context = MockContext::new(5, host_chain_height);
        let pruning_window = context.host_chain_history_size() as u64;
        let client_consensus_state_height = 10;

        let msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(
            client_consensus_state_height,
            host_chain_height.version_height,
        ))
        .unwrap();

        // The proof targets a height that does not exist (i.e., too advanced) on destination chain.
        let msg_height_advanced = MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(
            client_consensus_state_height,
            host_chain_height.increment().version_height,
        ))
        .unwrap();
        let pruned_height = host_chain_height
            .sub(pruning_window + 1)
            .unwrap()
            .version_height;
        // The consensus proof targets a missing height (pruned) on destination chain.
        let msg_height_old = MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(
            client_consensus_state_height,
            pruned_height,
        ))
        .unwrap();

        // The proofs in this message are created at a height which the client on destination chain does not have.
        let msg_proof_height_missing = MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(
            client_consensus_state_height - 1,
            host_chain_height.version_height,
        ))
        .unwrap();

        let try_conn_end = &ConnectionEnd::new(
            State::TryOpen,
            msg_conn_try.client_id().clone(),
            msg_conn_try.counterparty(),
            context.get_compatible_versions(),
        )
        .unwrap();

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because the height is too advanced".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_height_advanced)),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the height is too old".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_height_old)),
                want_pass: false,
            },
            Test {
                name: "Processing fails because no client exists".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_conn_try.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the client misses the consensus state targeted by the proof".to_string(),
                ctx: context.clone().with_client(msg_proof_height_missing.client_id(), Height::new(0, client_consensus_state_height)),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_proof_height_missing)),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the connection exists in the store already"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_connection(msg_conn_try.connection_id().clone(), try_conn_end.clone()),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_conn_try.clone())),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context.with_client(msg_conn_try.client_id(), Height::new(0, client_consensus_state_height)),
                msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_conn_try.clone())),
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
                        "conn_open_try: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have TryOpen state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_id, msg_conn_try.connection_id().clone());
                    assert_eq!(res.connection_end.state().clone(), State::TryOpen);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("connection_open_try".to_string()));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "conn_open_try: failed for test: {}, \nparams {:?} {:?} error: {:?}",
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
