//! Protocol logic specific to ICS3 messages of type `MsgConnectionOpenInit`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{ConnectionEnd, State};
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenInit;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;

pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenInit,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // No connection should exist.
    if ctx.connection_end(msg.connection_id()).is_some() {
        return Err(Kind::ConnectionExistsAlready(msg.connection_id().clone()).into());
    }

    // An IBC client running on the local (host) chain should exist.
    if ctx.client_state(msg.client_id()).is_none() {
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
    use std::convert::TryFrom;

    use crate::handler::EventType;
    use crate::ics03_connection::connection::{ConnectionEnd, State};
    use crate::ics03_connection::context::ConnectionReader;
    use crate::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::ConnectionMsg;
    use crate::mock_context::MockContext;
    use crate::Height;

    #[test]
    fn conn_open_init_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ConnectionMsg,
            want_pass: bool,
        }

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();
        let context = MockContext::default();

        let init_conn_end = &ConnectionEnd::new(
            State::Init,
            msg_conn_init.client_id().clone(),
            msg_conn_init.counterparty().clone(),
            context.get_compatible_versions(),
        )
        .unwrap();

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because the connection exists in the store already"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_connection(msg_conn_init.connection_id().clone(), init_conn_end.clone()),
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because no client exists in the context".to_string(),
                ctx: context.clone(),
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init.clone()),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context.with_client(msg_conn_init.client_id(), Height::new(0, 10)),
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init.clone()),
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
                        "conn_open_init: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have init state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_id, msg_conn_init.connection_id().clone());
                    assert_eq!(res.connection_end.state().clone(), State::Init);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("connection_open_init".to_string()));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "conn_open_init: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
