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

            // Apply the result to the context.
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
    use std::str::FromStr;

    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::msgs::{ClientMsg, MsgCreateAnyClient};
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics24_host::identifier::ClientId;
    use crate::ics26_routing::context_mock::MockICS26Context;
    use crate::ics26_routing::handler::dispatch;
    use crate::ics26_routing::msgs::ICS26Envelope;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::{MockClientState, MockConsensusState};
    use crate::Height;

    #[test]
    fn routing_dispatch() {
        struct DispatchParams {
            ctx: MockICS26Context,
            msg: ICS26Envelope,
        }
        struct Test {
            name: String,
            params: DispatchParams,
            want_pass: bool,
        }

        let msg = MsgCreateAnyClient {
            client_id: ClientId::from_str("client_id").unwrap(),
            client_type: ClientType::Mock,
            client_state: AnyClientState::from(MockClientState(MockHeader(Height::new(0, 42)))),
            consensus_state: AnyConsensusState::from(MockConsensusState(MockHeader(Height::new(
                0, 42,
            )))),
            signer: get_dummy_account_id(),
        };
        let envelope = ICS26Envelope::ICS2Msg(ClientMsg::CreateClient(msg));

        let params = DispatchParams {
            ctx: MockICS26Context::default(),
            msg: envelope,
        };

        let tests: Vec<Test> = vec![Test {
            name: "Client creation successful".to_string(),
            params,
            want_pass: true,
        }]
        .into_iter()
        .collect();

        for mut test in tests {
            let res = dispatch(&mut test.params.ctx, test.params.msg);

            assert_eq!(test.want_pass, res.is_ok(), "");

            // TODO: check the HandlerOutput.
            //
            // match res {
            //     Ok(()) => assert_eq!()
            //     // Err(_e) => assert_eq,
            // }
        }
    }
}
