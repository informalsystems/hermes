use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{ConnectionEnd, State};
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenInit;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::MsgConnectionOpenInit;

/// Protocol logic specific to ICS3 messages of type `MsgConnectionOpenInit`.
pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenInit,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // No connection should exist.
    if ctx.fetch_connection_end(msg.connection_id()).is_some() {
        return Err(Kind::ConnectionExistsAlready(msg.connection_id().clone()).into());
    }

    // An IBC client running on the local chain should exist.
    if ctx.fetch_client_state(msg.client_id()).is_none() {
        return Err(Kind::MissingClient(msg.client_id().clone()).into());
    }

    let new_connection_end = ConnectionEnd::new(
        State::Init,
        msg.client_id().clone(),
        msg.counterparty().clone(),
        ctx.get_compatible_versions(),
    )?;

    output.log("success: no connection found");

    let result = ConnectionResult {
        connection_id: msg.connection_id().clone(),
        connection_end: new_connection_end,
    };

    output.emit(ConnOpenInit(result.clone()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use crate::handler::EventType;
    use crate::ics03_connection::connection::{ConnectionEnd, State};
    use crate::ics03_connection::context::ConnectionReader;
    use crate::ics03_connection::context_mock::MockConnectionContext;
    use crate::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::ics03_connection::msgs::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::{ConnectionMsg, MsgConnectionOpenInit};
    use std::convert::TryFrom;

    #[test]
    fn conn_open_init_msg_processing() {
        struct Test {
            name: String,
            ctx: MockConnectionContext,
            msg: ConnectionMsg,
            want_pass: bool,
        }

        let dummy_msg = MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();
        let default_context = MockConnectionContext::new(34, 3);

        let init_conn_end = &ConnectionEnd::new(
            State::Init,
            dummy_msg.client_id().clone(),
            dummy_msg.counterparty().clone(),
            default_context.get_compatible_versions(),
        )
        .unwrap();

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                ctx: default_context
                    .clone()
                    .with_client_state(dummy_msg.client_id(), 10),
                msg: ConnectionMsg::ConnectionOpenInit(dummy_msg.clone()),
                want_pass: true,
            },
            Test {
                name: "Processing fails because no client exists in the context".to_string(),
                ctx: default_context.clone(),
                msg: ConnectionMsg::ConnectionOpenInit(dummy_msg.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because connection exists in the store already".to_string(),
                ctx: default_context
                    .add_connection(dummy_msg.connection_id().clone(), init_conn_end.clone()),
                msg: ConnectionMsg::ConnectionOpenInit(dummy_msg.clone()),
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for mut test in tests {
            // TODO - this is an example for testing with dispatch
            // TODO - the client tests use the process only. Need to select one approach and use the same across.
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

                    // The object in the output is a ConnectionEnd, should have init state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_id, dummy_msg.connection_id().clone());
                    assert_eq!(res.connection_end.state().clone(), State::Init);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("connection_open_init".to_string()));
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
