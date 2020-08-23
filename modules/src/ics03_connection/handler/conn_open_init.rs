use crate::ics03_connection::connection::{get_compatible_versions, ConnectionEnd, State};
use crate::ics03_connection::context::ICS3Context;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::Object;
use crate::ics03_connection::msgs::MsgConnectionOpenInit;

/// Protocol logic specific to ICS3 messages of type `MsgConnectionOpenInit`.
pub(crate) fn process(ctx: &dyn ICS3Context, msg: &MsgConnectionOpenInit) -> Result<Object, Error> {
    // No connection should exist.
    if ctx.fetch_connection_end(msg.connection_id()).is_some() {
        Err(Kind::ConnectionExistsAlready(msg.connection_id().clone()).into())
    } else {
        let mut new_connection_end = ConnectionEnd::new(
            msg.client_id().clone(),
            msg.counterparty().clone(),
            get_compatible_versions(),
        )?;
        new_connection_end.set_state(State::Init);

        Ok(new_connection_end)
    }
}

#[cfg(test)]
mod tests {
    use crate::events::IBCEvent;
    use crate::ics03_connection::connection::{get_compatible_versions, ConnectionEnd, State};
    use crate::ics03_connection::context_mock::MockContext;
    use crate::ics03_connection::handler::process_ics3_msg;
    use crate::ics03_connection::msgs::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::ICS3Msg;
    use tendermint::block::Height;

    #[test]
    fn conn_open_init_msg_processing() {
        #[derive(Clone, Debug)]
        struct ConnOpenInitProcessParams {
            ctx: MockContext,
            msg: ICS3Msg,
        }

        struct Test {
            name: String,
            params: ConnOpenInitProcessParams,
            want_pass: bool,
        }

        let dummy_msg = get_dummy_msg_conn_open_init();
        let dummy_conn_end = ConnectionEnd::new(
            dummy_msg.client_id().clone(),
            dummy_msg.counterparty().clone(),
            get_compatible_versions(),
        )
        .unwrap();

        let default_con_params = ConnOpenInitProcessParams {
            ctx: MockContext::new(),
            msg: ICS3Msg::ConnectionOpenInit(dummy_msg.clone()),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Good parameters, arbitrary chain height".to_string(),
                params: ConnOpenInitProcessParams {
                    ctx: MockContext::new().set_chain_height(Height(34)),
                    ..default_con_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Protocol fails because connection exists in the store already".to_string(),
                params: ConnOpenInitProcessParams {
                    ctx: MockContext::new()
                        .add_connection_to_store(dummy_msg.connection_id().clone(), dummy_conn_end),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = process_ics3_msg(&test.params.ctx, &test.params.msg);
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert_eq!(
                        test.want_pass,
                        true,
                        "process_ics3_msg() test passed but was supposed to fail for test: {}, \nparams {:?}",
                        test.name,
                        test.params.clone()
                    );
                    assert!(proto_output.object.is_some()); // An output object must exist.
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have init state.
                    proto_output.object.map(|conn_end| {
                        assert!(conn_end.state_matches(&State::Init));
                    });
                    for e in proto_output.events.iter() {
                        match e {
                            IBCEvent::OpenInitConnection(_event) => {
                                // TODO: Test `_event.height` against the chain height (must be equal).
                                // Currently such a test cannot compile b/c:
                                // "no implementation for `u64 == tendermint::block::height::Height`".
                                // Fixed with: https://github.com/informalsystems/ibc-rs/issues/191.
                                // assert_eq!(test.params.ctx.chain_current_height(), _event.height);
                            }
                            _ => panic!(
                                "process_ics3_msg() failed for test {}, \nparams {:?}",
                                test.name,
                                test.params.clone()
                            ),
                        }
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "process_ics3_msg() failed for test: {}, \nparams {:?} error: {:?}",
                        test.name,
                        test.params.clone(),
                        e,
                    );
                }
            }
        }
    }

    // TODO: the other processing functions + implementation for MockContext.
}
