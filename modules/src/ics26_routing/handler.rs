use prost_types::Any;
use tendermint_proto::Protobuf;

// use crate::handler;
use crate::events::IBCEvent;
use crate::handler::HandlerOutput;
use crate::ics02_client::handler::dispatch as ics2_msg_dispatcher;
use crate::ics02_client::msgs::create_client;
use crate::ics02_client::msgs::update_client;
use crate::ics02_client::msgs::ClientMsg;
use crate::ics03_connection::handler::dispatch as ics3_msg_dispatcher;
use crate::ics04_channel::handler::dispatch as ics4_msg_dispatcher;

use crate::ics26_routing::context::ICS26Context;
use crate::ics26_routing::error::{Error, Kind};
use crate::ics26_routing::msgs::ICS26Envelope;
use crate::ics26_routing::msgs::ICS26Envelope::{ICS2Msg, ICS3Msg, ICS4Msg};

/// Mimics the DeliverTx ABCI interface, but a slightly lower level. No need for authentication
/// info or signature checks here.
/// https://github.com/cosmos/cosmos-sdk/tree/master/docs/basics
/// Returns a vector of all events that got generated as a byproduct of processing `messages`.
pub fn deliver<Ctx>(ctx: &mut Ctx, messages: Vec<Any>) -> Result<Vec<IBCEvent>, Error>
where
    Ctx: ICS26Context,
{
    // Create a clone, which will store each intermediary stage of applying txs.
    let mut ctx_interim = ctx.clone();

    // A buffer for all the events, to be used as return value.
    let mut res: Vec<IBCEvent> = vec![];

    for any_msg in messages {
        // Decode the proto message into a domain message, creating an ICS26 envelope.
        let envelope = match any_msg.type_url.as_str() {
            // ICS2 messages
            create_client::TYPE_URL => {
                // Pop out the message and then wrap it in the corresponding type.
                let domain_msg = create_client::MsgCreateAnyClient::decode_vec(&any_msg.value)
                    .map_err(|e| Kind::MalformedMessageBytes.context(e))?;
                Ok(ICS2Msg(ClientMsg::CreateClient(domain_msg)))
            }
            update_client::TYPE_URL => {
                let domain_msg = update_client::MsgUpdateAnyClient::decode_vec(&any_msg.value)
                    .map_err(|e| Kind::MalformedMessageBytes.context(e))?;
                Ok(ICS2Msg(ClientMsg::UpdateClient(domain_msg)))
            }
            // TODO: ICS3 messages
            _ => Err(Kind::UnknownMessageTypeURL(any_msg.type_url)),
        }?;

        // Process the envelope, and accumulate any events that were generated.
        let mut output = dispatch(&mut ctx_interim, envelope)?;
        // TODO: output.log and output.result are discarded
        res.append(&mut output.events);
    }

    // No error has surfaced, so we now apply the changes permanently to the original context.
    *ctx = ctx_interim;
    Ok(res)
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
        }

        ICS4Msg(msg) => {
            let handler_output =
                ics4_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e))?;

            // Apply any results to the host chain store.
            ctx.store_channel_result(handler_output.result)
                .map_err(|e| Kind::KeeperRaisedError.context(e))?;

            HandlerOutput::builder()
                .with_log(handler_output.log)
                .with_events(handler_output.events)
                .with_result(())
        } // TODO: add dispatchers for others.
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::ics02_client::msgs::create_client::MsgCreateAnyClient;
    use crate::ics02_client::msgs::update_client::MsgUpdateAnyClient;
    use crate::ics02_client::msgs::ClientMsg;
    use crate::ics03_connection::msgs::conn_open_ack::{
        test_util::get_dummy_msg_conn_open_ack_ics26, MsgConnectionOpenAck,
    };
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init_ics26;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::conn_open_try::test_util::get_dummy_msg_conn_open_try;
    use crate::ics03_connection::msgs::conn_open_try::test_util::get_dummy_msg_conn_open_try_ics26;
    use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
    use crate::ics03_connection::msgs::ConnectionMsg;
    use crate::ics04_channel::msgs::{
        chan_close_confirm::test_util::get_dummy_raw_msg_chan_close_confirm_ics26,
        chan_close_init::{test_util::get_dummy_raw_msg_chan_close_init, MsgChannelCloseInit},
    };
    use crate::ics04_channel::msgs::{
        chan_open_ack::{test_util::get_dummy_raw_msg_chan_open_ack_ics26, MsgChannelOpenAck},
        chan_open_init::test_util::get_dummy_raw_msg_chan_open_init_ics26,
        chan_open_try::test_util::get_dummy_raw_msg_chan_open_try_ics26,
    };
    use crate::{
        ics02_client::client_def::{AnyClientState, AnyConsensusState},
        ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm,
    };

    use crate::ics04_channel::msgs::chan_open_init::test_util::get_dummy_raw_msg_chan_open_init_with_missing_connection;
    use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
    use crate::ics04_channel::msgs::ChannelMsg;
    use crate::ics24_host::identifier::ChannelId;

    use crate::events::IBCEvent;
    use crate::ics26_routing::handler::dispatch;
    use crate::ics26_routing::msgs::ICS26Envelope;
    use crate::mock::client_state::{MockClientState, MockConsensusState};
    use crate::mock::context::MockContext;
    use crate::mock::header::MockHeader;
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
        let default_signer = get_dummy_account_id();
        let start_client_height = Height::new(0, 5);
        let update_client_height = Height::new(0, 34);

        let create_client_msg = MsgCreateAnyClient::new(
            AnyClientState::from(MockClientState(MockHeader(start_client_height))),
            AnyConsensusState::from(MockConsensusState(MockHeader(start_client_height))),
            get_dummy_account_id(),
        )
        .unwrap();

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init_ics26()).unwrap();

        let correct_msg_conn_try =
            MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try_ics26(5, 5)).unwrap();

        let msg_conn_ack =
            MsgConnectionOpenAck::try_from(get_dummy_msg_conn_open_ack_ics26(5, 5)).unwrap();

        let msg_conn_try_good_height =
            MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(10, 29)).unwrap();

        let msg_chan_init =
            MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init_ics26()).unwrap();

        let msg_chan_init2 = MsgChannelOpenInit::try_from(
            get_dummy_raw_msg_chan_open_init_with_missing_connection(),
        )
        .unwrap();

        let proof_height = 5;

        let mut msg_chan_try2 =
            MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try_ics26(proof_height))
                .unwrap();

        // We reuse this same context across all tests. Nothing in particular needs parametrizing.
        let mut ctx = MockContext::default();

        let prefix = ChannelId::default().to_string();
        let suffix = 0;
        msg_chan_try2.previous_channel_id = Some(
            <ChannelId as FromStr>::from_str(format!("{}-{}", prefix, suffix).as_str()).unwrap(),
        );

        let msg_chan_ack =
            MsgChannelOpenAck::try_from(get_dummy_raw_msg_chan_open_ack_ics26(proof_height))
                .unwrap();

        let mut msg_chan_close_init =
            MsgChannelCloseInit::try_from(get_dummy_raw_msg_chan_close_init()).unwrap();

        let msg_chan_close_confirm = MsgChannelCloseConfirm::try_from(
            get_dummy_raw_msg_chan_close_confirm_ics26(proof_height),
        )
        .unwrap();

        msg_chan_close_init.channel_id = ChannelId::from_str("defaultChannel-0").unwrap();

        // First, create a client..
        let res = dispatch(
            &mut ctx,
            ICS26Envelope::ICS2Msg(ClientMsg::CreateClient(create_client_msg.clone())),
        );

        assert_eq!(
            true,
            res.is_ok(),
            "ICS26 routing dispatch test 'client creation' failed for message {:?} with result: {:?}",
            create_client_msg,
            res
        );

        ctx.add_port(msg_chan_init.port_id().clone());

        // Figure out the ID of the client that was just created.
        let mut events = res.unwrap().events;
        let client_id_event = events.pop();
        assert!(
            client_id_event.is_some(),
            "There was no event generated for client creation!"
        );
        let client_id = match client_id_event.unwrap() {
            IBCEvent::CreateClient(create_client) => create_client.client_id().clone(),
            event => panic!("unexpected IBC event: {:?}", event),
        };

        let incorrect_msg_conn_try =
            MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try_ics26(10, 43)).unwrap();

        let tests: Vec<Test> = vec![
            // Test some ICS2 client functionality.
            Test {
                name: "Client update successful".to_string(),
                msg: ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: client_id.clone(),
                    header: MockHeader(update_client_height).into(),
                    signer: default_signer,
                })),
                want_pass: true,
            },
            Test {
                name: "Client update fails due to stale header".to_string(),
                msg: ICS26Envelope::ICS2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: client_id.clone(),
                    header: MockHeader(update_client_height).into(),
                    signer: default_signer,
                })),
                want_pass: false,
            },
            Test {
                name: "Connection open init it succeeds".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenInit(
                    msg_conn_init.with_client_id(client_id),
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
                name: "Connection open try succeeds".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    correct_msg_conn_try,
                ))),
                want_pass: true,
            },
            Test {
                name: "Connection open ack succeeds".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenAck(Box::new(
                    msg_conn_ack,
                ))),
                want_pass: true,
            },
            Test {
                name: "Connection open try fails due to mismatching connection ends".to_string(),
                msg: ICS26Envelope::ICS3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    msg_conn_try_good_height,
                ))),
                want_pass: false,
            },
            // ICS04
            Test {
                name: "Channel open init succeeds".to_string(),
                msg: ICS26Envelope::ICS4Msg(ChannelMsg::ChannelOpenInit(msg_chan_init)),
                want_pass: true,
            },
            Test {
                name: "Channel open init fail due to missing connection".to_string(),
                msg: ICS26Envelope::ICS4Msg(ChannelMsg::ChannelOpenInit(msg_chan_init2)),
                want_pass: false,
            },
            Test {
                name: "Channel open try succedes".to_string(),
                msg: ICS26Envelope::ICS4Msg(ChannelMsg::ChannelOpenTry(msg_chan_try2)),
                want_pass: true,
            },
            Test {
                name: "Channel open ack succedes".to_string(),
                msg: ICS26Envelope::ICS4Msg(ChannelMsg::ChannelOpenAck(msg_chan_ack)),
                want_pass: true,
            },
            Test {
                name: "Channel close init succedes".to_string(),
                msg: ICS26Envelope::ICS4Msg(ChannelMsg::ChannelCloseInit(msg_chan_close_init)),
                want_pass: true,
            },
            Test {
                name: "Channel close confirm fails cause channel is already closed".to_string(),
                msg: ICS26Envelope::ICS4Msg(ChannelMsg::ChannelCloseConfirm(
                    msg_chan_close_confirm,
                )),
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
