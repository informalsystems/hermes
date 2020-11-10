use crate::handler::HandlerOutput;
use crate::ics02_client::handler::dispatch as ics2_msg_dispatcher;
use crate::ics03_connection::handler::dispatch as ics3_msg_dispatcher;
use crate::ics26_routing::context::ICS26Context;
use crate::ics26_routing::error::{Error, Kind};
use crate::ics26_routing::msgs::ICS26Envelope;
use crate::ics26_routing::msgs::ICS26Envelope::{ICS2Msg, ICS3Msg};
use ibc_proto::cosmos::tx::v1beta1::Tx;

// TODO: Implement this (the tx type is probably wrong also). Rough sketch:
// 1. deserialize & validate each message in the tx
// 2. invoke dispatch(ctx, ms)
// 3. if all message in the tx pass through correctly, then apply the side-effects to the context
pub fn deliver_tx<Ctx>(_ctx: &mut Ctx, _tx: Tx) -> Result<(), Error>
where
    Ctx: ICS26Context,
{
    unimplemented!()
}

/// Top-level ICS dispatch function. Routes incoming IBC messages to their corresponding module.
/// Returns a handler output with empty result of type `HandlerOutput<()>` which contains the log
/// and events produced after processing the input `msg`.
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: ICS26Envelope) -> Result<HandlerOutput<()>, Error>
where
    Ctx: ICS26Context,
{
    let output = match msg {
        ICS2Msg(msg) => {
            let handler_output =
                ics2_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e))?;

            // Apply the result to the context (host chain store).
            ctx.store_client_result(handler_output.result)
                .map_err(|e| Kind::KeeperRaisedError.context(e))?;

            HandlerOutput::builder()
                .with_log(handler_output.log)
                .with_events(handler_output.events)
                .with_result(())
        }

        ICS3Msg(msg) => {
            let handler_output =
                ics3_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e))?;

            // Apply any results to the host chain store.
            ctx.store_connection_result(handler_output.result)
                .map_err(|e| Kind::KeeperRaisedError.context(e))?;

            HandlerOutput::builder()
                .with_log(handler_output.log)
                .with_events(handler_output.events)
                .with_result(())
        } // TODO: add dispatchers for ICS4 and others.
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::msgs::create_client::MsgCreateAnyClient;
    use crate::ics02_client::msgs::update_client::MsgUpdateAnyClient;
    use crate::ics02_client::msgs::ClientMsg;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::conn_open_try::test_util::get_dummy_msg_conn_open_try;
    use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
    use crate::ics03_connection::msgs::ConnectionMsg;
    use crate::ics24_host::identifier::ClientId;
    use crate::ics26_routing::handler::dispatch;
    use crate::ics26_routing::msgs::ICS26Envelope;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::{MockClientState, MockConsensusState};
    use crate::mock_context::MockContext;
    use crate::test_utils::get_dummy_account_id;
    use crate::Height;

    #[test]
    // These tests exercise two main paths: (1) the ability of the ICS26 routing module to dispatch
    // messages to the correct module handler, and more importantly: (2) the ability of ICS handlers
    // to work with the context and correctly store results (i.e., the ClientKeeper and
    // ConnectionKeeper traits).
    fn routing_module_and_keepers() {
        // Test parameters
        struct Test {
            name: String,
            msg: ICS26Envelope,
            want_pass: bool,
        }
        let default_client_id = ClientId::from_str("client_id").unwrap();
        let default_signer = get_dummy_account_id();
        let start_client_height = Height::new(0, 42);
        let update_client_height = Height::new(0, 50);

        let create_client_msg = MsgCreateAnyClient::new(
            ClientId::from_str("client_id").unwrap(),
            AnyClientState::from(MockClientState(MockHeader(start_client_height))),
            AnyConsensusState::from(MockConsensusState(MockHeader(start_client_height))),
            get_dummy_account_id(),
        )
        .unwrap();

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();
        let incorrect_msg_conn_try =
            MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(10, 34)).unwrap();
        let msg_conn_try_good_height =
            MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(10, 29)).unwrap();

        // We reuse this same context across all tests. Nothing in particular needs parametrizing.
        let mut ctx = MockContext::default();

        let tests: Vec<Test> = vec![
            // Test the ICS2 client functionality.
            Test {
                name: "Client creation successful".to_string(),
                msg: ICS26Envelope::ICS2Msg(ClientMsg::CreateClient(create_client_msg)),
                want_pass: true,
            },
            Test {
                name: "Client update successful".to_string(),
                msg: ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: default_client_id.clone(),
                    header: MockHeader(update_client_height).into(),
                    signer: default_signer,
                })),
                want_pass: true,
            },
            Test {
                name: "Client update fails due to stale header".to_string(),
                msg: ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: default_client_id.clone(),
                    header: MockHeader(update_client_height).into(),
                    signer: default_signer,
                })),
                want_pass: false,
            },
            // Test the ICS3 connection functionality.
            Test {
                name: "Connection open init fail due to missing client".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenInit(
                    msg_conn_init.clone(),
                )),
                want_pass: false,
            },
            Test {
                name: "Connection open init success".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenInit(
                    msg_conn_init.with_client_id(default_client_id),
                )),
                want_pass: true,
            },
            Test {
                name: "Connection open try fails due to InvalidConsensusHeight (too high)"
                    .to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    incorrect_msg_conn_try,
                ))),
                want_pass: false,
            },
            Test {
                name: "Connection open try fails due to mismatching connection ends".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    msg_conn_try_good_height,
                ))),
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = dispatch(&mut ctx, test.msg.clone());

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "ICS26 routing dispatch test '{}' failed for message {:?} with result: {:?}",
                test.name,
                test.msg,
                res
            );
        }
    }
}
