//! Protocol logic specific to ICS3 messages of type `MsgConnectionOpenInit`.

use crate::core::ics03_connection::connection::{ConnectionEnd, State};
use crate::core::ics03_connection::context::ConnectionReader;
use crate::core::ics03_connection::error::Error;
use crate::core::ics03_connection::events::Attributes;
use crate::core::ics03_connection::handler::{ConnectionIdState, ConnectionResult};
use crate::core::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use crate::core::ics24_host::identifier::ConnectionId;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;

pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenInit,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // An IBC client running on the local (host) chain should exist.
    ctx.client_state(&msg.client_id)?;

    let versions = match msg.version {
        Some(version) => {
            if ctx.get_compatible_versions().contains(&version) {
                Ok(vec![version])
            } else {
                Err(Error::version_not_supported(version))
            }
        }
        None => Ok(ctx.get_compatible_versions()),
    }?;

    let new_connection_end = ConnectionEnd::new(
        State::Init,
        msg.client_id.clone(),
        msg.counterparty.clone(),
        versions,
        msg.delay_period,
    );

    // Construct the identifier for the new connection.
    let id_counter = ctx.connection_counter()?;
    let conn_id = ConnectionId::new(id_counter);

    output.log(format!(
        "success: generated new connection identifier: {}",
        conn_id
    ));

    let result = ConnectionResult {
        connection_id: conn_id.clone(),
        connection_id_state: ConnectionIdState::Generated,
        connection_end: new_connection_end,
    };

    let event_attributes = Attributes {
        connection_id: Some(conn_id),
        height: ctx.host_current_height(),
        ..Default::default()
    };
    output.emit(IbcEvent::OpenInitConnection(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use crate::core::ics03_connection::connection::State;
    use crate::core::ics03_connection::context::ConnectionReader;
    use crate::core::ics03_connection::handler::{dispatch, ConnectionResult};
    use crate::core::ics03_connection::msgs::conn_open_init::test_util::get_dummy_raw_msg_conn_open_init;
    use crate::core::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::core::ics03_connection::msgs::ConnectionMsg;
    use crate::core::ics03_connection::version::Version;
    use crate::events::IbcEvent;
    use crate::mock::context::MockContext;
    use crate::prelude::*;
    use crate::Height;

    use ibc_proto::ibc::core::connection::v1::Version as RawVersion;

    #[test]
    fn conn_open_init_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ConnectionMsg,
            expected_versions: Vec<Version>,
            want_pass: bool,
        }

        let msg_conn_init_default =
            MsgConnectionOpenInit::try_from(get_dummy_raw_msg_conn_open_init()).unwrap();
        let msg_conn_init_no_version = MsgConnectionOpenInit {
            version: None,
            ..msg_conn_init_default.clone()
        };
        let msg_conn_init_bad_version = MsgConnectionOpenInit {
            version: Version::try_from(RawVersion {
                identifier: "random identifier 424242".to_string(),
                features: vec![],
            })
            .unwrap()
            .into(),
            ..msg_conn_init_default.clone()
        };
        let default_context = MockContext::default();
        let good_context = default_context
            .clone()
            .with_client(&msg_conn_init_default.client_id, Height::new(0, 10));

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no client exists in the context".to_string(),
                ctx: default_context,
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_default.clone()),
                expected_versions: vec![msg_conn_init_default.version.clone().unwrap()],
                want_pass: false,
            },
            Test {
                name: "Incompatible version in MsgConnectionOpenInit msg".to_string(),
                ctx: good_context.clone(),
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_bad_version),
                expected_versions: vec![],
                want_pass: false,
            },
            Test {
                name: "No version in MsgConnectionOpenInit msg".to_string(),
                ctx: good_context.clone(),
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_no_version),
                expected_versions: good_context.get_compatible_versions(),
                want_pass: true,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: good_context,
                msg: ConnectionMsg::ConnectionOpenInit(msg_conn_init_default.clone()),
                expected_versions: vec![msg_conn_init_default.version.unwrap()],
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
                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have init state.
                    let res: ConnectionResult = proto_output.result;
                    assert_eq!(res.connection_end.state().clone(), State::Init);

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::OpenInitConnection(_)));
                        assert_eq!(e.height(), test.ctx.host_current_height());
                    }

                    assert_eq!(res.connection_end.versions(), test.expected_versions);

                    // This needs to be last
                    assert!(
                        test.want_pass,
                        "conn_open_init: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
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
