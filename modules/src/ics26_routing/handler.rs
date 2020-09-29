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
    use crate::handler::HandlerOutput;
    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::context_mock::MockClientContext;
    use crate::ics02_client::msgs::{ClientMsg, MsgCreateAnyClient, MsgUpdateAnyClient};
    use crate::ics02_client::state::ClientState;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics24_host::identifier::ClientId;
    use crate::ics26_routing::context_mock::MockICS26Context;
    use crate::ics26_routing::error::{Error, Kind};
    use crate::ics26_routing::handler::dispatch;
    use crate::ics26_routing::msgs::ICS26Envelope;
    use crate::mock_client::header::MockHeader;
    use crate::mock_client::state::{MockClientState, MockConsensusState};
    use std::str::FromStr;
    use tendermint::block::Height;

    fn update_client_to_latest(
        dest: &mut MockICS26Context,
        src: &MockICS26Context,
        client_id: &ClientId,
    ) -> Result<HandlerOutput<()>, Error> {
        // Check if client for ibc0 on ibc1 has been updated to latest height:
        // - query latest height on source chain
        // TODO maybe: src.get_latest_height()
        let src_latest_height = src.chain_context().latest;
        // - query client state on destination chain
        //  (TODO - simulate relayer by "querying" the client state and get the latest height from there
        //  then check if that is smaller than the source latest height)
        // TODO maybe: dest.query_client_state(client_id)
        let dest_client = dest.client_context.clients.get(&client_id).unwrap();

        // let dest_height = dest.query_client_full_state(client_id).latest_height()?;
        // if dest_height > src_latest_height {
        //      weird
        // }
        // if dest_height < src_latest_height {
        //      return new Envelope
        // }

        // Does the client have a consensus state for the latest height?
        if dest_client
            .consensus_states
            .get(&src_latest_height)
            .is_none()
        {
            // No, client needs update.
            let msg = MsgUpdateAnyClient {
                client_id: client_id.clone(),
                header: MockHeader(Height(u64::from(src_latest_height))).into(),
                signer: get_dummy_account_id(),
            };
            dispatch(dest, ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(msg)))
        } else {
            Err(Into::<Error>::into(Kind::HandlerRaisedError))
        }
    }

    #[test]
    fn test_update_two_chains() {
        let client_on_ibc0_for_ibc1 = ClientId::from_str("ibconeclient").unwrap();
        let client_on_ibc1_for_ibc0 = ClientId::from_str("ibczeroclient").unwrap();

        let ibc0_start_height = 11;
        let ibc1_start_height = 20;
        let max_history_size = 3;
        let num_iterations = 4;

        // Create ibc0 context
        let mut ctx_ibc0_clients = MockClientContext::new(ibc0_start_height, max_history_size);
        ctx_ibc0_clients.with_client(
            &client_on_ibc0_for_ibc1,
            ClientType::Mock,
            Height(ibc1_start_height),
        );
        let mut ctx_ibc0 = MockICS26Context {
            client_context: ctx_ibc0_clients,
            connection_context: Default::default(),
        };

        // Create ibc1 context
        let mut ctx_ibc1_clients = MockClientContext::new(ibc1_start_height, max_history_size);
        ctx_ibc1_clients.with_client(
            &client_on_ibc1_for_ibc0,
            ClientType::Mock,
            Height(ibc0_start_height - 1),
        );
        let mut ctx_ibc1 = MockICS26Context {
            client_context: ctx_ibc1_clients,
            connection_context: Default::default(),
        };

        // Loop a number of times, create new blocks and ensure clients on chain are updated to latest height.
        for _i in 0..num_iterations {
            // Update client on ibc1
            let res = update_client_to_latest(&mut ctx_ibc1, &ctx_ibc0, &client_on_ibc1_for_ibc0);
            assert!(res.is_ok());
            assert_eq!(
                ctx_ibc1
                    .client_context()
                    .clients
                    .get(&client_on_ibc1_for_ibc0)
                    .unwrap()
                    .client_state
                    .latest_height(),
                ctx_ibc0.chain_context().latest
            );

            // Advance height on ibc1
            let mut chain_context = ctx_ibc1.chain_context().clone();
            chain_context.add_header(0);
            ctx_ibc1.set_chain_context(chain_context);

            // Update client on ibc0
            let res = update_client_to_latest(&mut ctx_ibc0, &ctx_ibc1, &client_on_ibc0_for_ibc1);
            assert!(res.is_ok());
            assert_eq!(
                ctx_ibc0
                    .client_context()
                    .clients
                    .get(&client_on_ibc0_for_ibc1)
                    .unwrap()
                    .client_state
                    .latest_height(),
                ctx_ibc1.chain_context().latest
            );

            // Advance height on ibc0
            let mut chain_context = ctx_ibc0.chain_context().clone();
            chain_context.add_header(0);
            ctx_ibc0.set_chain_context(chain_context);
        }
    }

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
            client_state: AnyClientState::from(MockClientState(MockHeader(Height(42)))),
            consensus_state: AnyConsensusState::from(MockConsensusState(MockHeader(Height(42)))),
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
