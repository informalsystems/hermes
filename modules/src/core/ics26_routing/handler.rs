use crate::prelude::*;

use ibc_proto::google::protobuf::Any;

use crate::applications::ics20_fungible_token_transfer::relay_application_logic::send_transfer::send_transfer as ics20_msg_dispatcher;
use crate::core::ics02_client::handler::dispatch as ics2_msg_dispatcher;
use crate::core::ics03_connection::handler::dispatch as ics3_msg_dispatcher;
use crate::core::ics04_channel::handler::{
    channel_callback as ics4_callback, channel_dispatch as ics4_msg_dispatcher,
    channel_validate as ics4_validate, recv_packet::RecvPacketResult,
};
use crate::core::ics04_channel::handler::{
    get_module_for_packet_msg, packet_callback as ics4_packet_callback,
    packet_dispatch as ics4_packet_msg_dispatcher,
};
use crate::core::ics04_channel::packet::PacketResult;
use crate::core::ics26_routing::context::Ics26Context;
use crate::core::ics26_routing::error::Error;
use crate::core::ics26_routing::msgs::Ics26Envelope::{
    self, Ics20Msg, Ics2Msg, Ics3Msg, Ics4ChannelMsg, Ics4PacketMsg,
};
use crate::{events::IbcEvent, handler::HandlerOutput};

/// Mimics the DeliverTx ABCI interface, but for a single message and at a slightly lower level.
/// No need for authentication info or signature checks here.
/// Returns a vector of all events that got generated as a byproduct of processing `message`.
pub fn deliver<Ctx>(ctx: &mut Ctx, message: Any) -> Result<(Vec<IbcEvent>, Vec<String>), Error>
where
    Ctx: Ics26Context,
{
    // Decode the proto message into a domain message, creating an ICS26 envelope.
    let envelope = decode(message)?;

    // Process the envelope, and accumulate any events that were generated.
    let output = dispatch(ctx, envelope)?;

    Ok((output.events, output.log))
}

/// Attempts to convert a message into a [Ics26Envelope] message
pub fn decode(message: Any) -> Result<Ics26Envelope, Error> {
    message.try_into()
}

/// Top-level ICS dispatch function. Routes incoming IBC messages to their corresponding module.
/// Returns a handler output with empty result of type `HandlerOutput<()>` which contains the log
/// and events produced after processing the input `msg`.
/// If this method returns an error, the runtime is expected to rollback all state modifications to
/// the `Ctx` caused by all messages from the transaction that this `msg` is a part of.
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: Ics26Envelope) -> Result<HandlerOutput<()>, Error>
where
    Ctx: Ics26Context,
{
    let output = match msg {
        Ics2Msg(msg) => {
            let handler_output = ics2_msg_dispatcher(ctx, msg).map_err(Error::ics02_client)?;

            // Apply the result to the context (host chain store).
            ctx.store_client_result(handler_output.result)
                .map_err(Error::ics02_client)?;

            HandlerOutput::builder()
                .with_log(handler_output.log)
                .with_events(handler_output.events)
                .with_result(())
        }

        Ics3Msg(msg) => {
            let handler_output = ics3_msg_dispatcher(ctx, msg).map_err(Error::ics03_connection)?;

            // Apply any results to the host chain store.
            ctx.store_connection_result(handler_output.result)
                .map_err(Error::ics03_connection)?;

            HandlerOutput::builder()
                .with_log(handler_output.log)
                .with_events(handler_output.events)
                .with_result(())
        }

        Ics4ChannelMsg(msg) => {
            let module_id = ics4_validate(ctx, &msg).map_err(Error::ics04_channel)?;
            let (mut handler_builder, channel_result) =
                ics4_msg_dispatcher(ctx, &msg).map_err(Error::ics04_channel)?;

            let mut module_output = HandlerOutput::builder().with_result(());
            let cb_result =
                ics4_callback(ctx, &module_id, &msg, channel_result, &mut module_output);
            handler_builder.merge(module_output);
            let channel_result = cb_result.map_err(Error::ics04_channel)?;

            // Apply any results to the host chain store.
            ctx.store_channel_result(channel_result)
                .map_err(Error::ics04_channel)?;

            handler_builder.with_result(())
        }

        Ics20Msg(msg) => {
            let handler_output =
                ics20_msg_dispatcher(ctx, msg).map_err(Error::ics20_fungible_token_transfer)?;

            // Apply any results to the host chain store.
            ctx.store_packet_result(handler_output.result)
                .map_err(Error::ics04_channel)?;

            HandlerOutput::builder()
                .with_log(handler_output.log)
                .with_events(handler_output.events)
                .with_result(())
        }

        Ics4PacketMsg(msg) => {
            let module_id = get_module_for_packet_msg(ctx, &msg).map_err(Error::ics04_channel)?;
            let (mut handler_builder, packet_result) =
                ics4_packet_msg_dispatcher(ctx, &msg).map_err(Error::ics04_channel)?;

            if matches!(packet_result, PacketResult::Recv(RecvPacketResult::NoOp)) {
                return Ok(handler_builder.with_result(()));
            }

            let mut module_output = HandlerOutput::builder().with_result(());
            let cb_result = ics4_packet_callback(ctx, &module_id, &msg, &mut module_output);
            handler_builder.merge(module_output);
            cb_result.map_err(Error::ics04_channel)?;

            // Apply any results to the host chain store.
            ctx.store_packet_result(packet_result)
                .map_err(Error::ics04_channel)?;

            handler_builder.with_result(())
        }
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use test_log::test;

    use crate::core::ics02_client::client_consensus::AnyConsensusState;
    use crate::core::ics02_client::client_state::AnyClientState;
    use crate::events::IbcEvent;
    use crate::{
        applications::ics20_fungible_token_transfer::msgs::transfer::test_util::get_dummy_msg_transfer,
        core::ics23_commitment::commitment::test_util::get_dummy_merkle_proof,
    };

    use crate::core::ics02_client::msgs::{
        create_client::MsgCreateAnyClient, update_client::MsgUpdateAnyClient,
        upgrade_client::MsgUpgradeAnyClient, ClientMsg,
    };
    use crate::core::ics03_connection::msgs::{
        conn_open_ack::{test_util::get_dummy_raw_msg_conn_open_ack, MsgConnectionOpenAck},
        conn_open_init::{test_util::get_dummy_raw_msg_conn_open_init, MsgConnectionOpenInit},
        conn_open_try::{test_util::get_dummy_raw_msg_conn_open_try, MsgConnectionOpenTry},
        ConnectionMsg,
    };
    use crate::core::ics04_channel::msgs::{
        chan_close_confirm::{
            test_util::get_dummy_raw_msg_chan_close_confirm, MsgChannelCloseConfirm,
        },
        chan_close_init::{test_util::get_dummy_raw_msg_chan_close_init, MsgChannelCloseInit},
        chan_open_ack::{test_util::get_dummy_raw_msg_chan_open_ack, MsgChannelOpenAck},
        chan_open_init::{test_util::get_dummy_raw_msg_chan_open_init, MsgChannelOpenInit},
        chan_open_try::{test_util::get_dummy_raw_msg_chan_open_try, MsgChannelOpenTry},
        recv_packet::{test_util::get_dummy_raw_msg_recv_packet, MsgRecvPacket},
        timeout_on_close::{test_util::get_dummy_raw_msg_timeout_on_close, MsgTimeoutOnClose},
        ChannelMsg, PacketMsg,
    };

    use crate::core::ics24_host::identifier::ConnectionId;
    use crate::core::ics26_routing::context::{ModuleId, RouterBuilder};
    use crate::core::ics26_routing::handler::dispatch;
    use crate::core::ics26_routing::msgs::Ics26Envelope;
    use crate::mock::client_state::{MockClientState, MockConsensusState};
    use crate::mock::context::{MockContext, MockRouterBuilder};
    use crate::mock::header::MockHeader;
    use crate::test_utils::{get_dummy_account_id, DummyModule};
    use crate::timestamp::Timestamp;
    use crate::Height;

    #[test]
    /// These tests exercise two main paths: (1) the ability of the ICS26 routing module to dispatch
    /// messages to the correct module handler, and more importantly: (2) the ability of ICS handlers
    /// to work with the context and correctly store results (i.e., the `ClientKeeper`,
    /// `ConnectionKeeper`, and `ChannelKeeper` traits).
    fn routing_module_and_keepers() {
        // Test parameters
        struct Test {
            name: String,
            msg: Ics26Envelope,
            want_pass: bool,
        }
        let default_signer = get_dummy_account_id();
        let client_height = 5;
        let start_client_height = Height::new(0, client_height);
        let update_client_height = Height::new(0, 34);
        let update_client_height_after_send = Height::new(0, 35);

        let update_client_height_after_second_send = Height::new(0, 36);

        let upgrade_client_height = Height::new(1, 2);

        let upgrade_client_height_second = Height::new(1, 1);

        let module = DummyModule::default();
        let module_id: ModuleId = "dummymodule".parse().unwrap();

        let router = MockRouterBuilder::default()
            .add_route(module_id.clone(), module)
            .unwrap()
            .build();

        // We reuse this same context across all tests. Nothing in particular needs parametrizing.
        let mut ctx = MockContext::default().with_router(router);

        let create_client_msg = MsgCreateAnyClient::new(
            AnyClientState::from(MockClientState::new(MockHeader::new(start_client_height))),
            AnyConsensusState::Mock(MockConsensusState::new(MockHeader::new(
                start_client_height,
            ))),
            default_signer.clone(),
        )
        .unwrap();

        //
        // Connection handshake messages.
        //
        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_raw_msg_conn_open_init()).unwrap();

        let correct_msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
            client_height,
            client_height,
        ))
        .unwrap();

        // The handler will fail to process this msg because the client height is too advanced.
        let incorrect_msg_conn_try = MsgConnectionOpenTry::try_from(
            get_dummy_raw_msg_conn_open_try(client_height + 1, client_height + 1),
        )
        .unwrap();

        let msg_conn_ack = MsgConnectionOpenAck::try_from(get_dummy_raw_msg_conn_open_ack(
            client_height,
            client_height,
        ))
        .unwrap();

        //
        // Channel handshake messages.
        //
        let msg_chan_init =
            MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init()).unwrap();

        // The handler will fail to process this b/c the associated connection does not exist
        let mut incorrect_msg_chan_init = msg_chan_init.clone();
        incorrect_msg_chan_init.channel.connection_hops = vec![ConnectionId::new(590)];

        let msg_chan_try =
            MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(client_height)).unwrap();

        let msg_chan_ack =
            MsgChannelOpenAck::try_from(get_dummy_raw_msg_chan_open_ack(client_height)).unwrap();

        let msg_chan_close_init =
            MsgChannelCloseInit::try_from(get_dummy_raw_msg_chan_close_init()).unwrap();

        let msg_chan_close_confirm =
            MsgChannelCloseConfirm::try_from(get_dummy_raw_msg_chan_close_confirm(client_height))
                .unwrap();

        let msg_transfer = get_dummy_msg_transfer(35);
        let msg_transfer_two = get_dummy_msg_transfer(36);

        let mut msg_to_on_close =
            MsgTimeoutOnClose::try_from(get_dummy_raw_msg_timeout_on_close(36, 5)).unwrap();
        msg_to_on_close.packet.sequence = 2.into();
        msg_to_on_close.packet.timeout_height = msg_transfer_two.timeout_height;
        msg_to_on_close.packet.timeout_timestamp = msg_transfer_two.timeout_timestamp;

        let msg_recv_packet = MsgRecvPacket::try_from(get_dummy_raw_msg_recv_packet(35)).unwrap();

        // First, create a client..
        let res = dispatch(
            &mut ctx,
            Ics26Envelope::Ics2Msg(ClientMsg::CreateClient(create_client_msg.clone())),
        );

        assert!(
            res.is_ok(),
            "ICS26 routing dispatch test 'client creation' failed for message {:?} with result: {:?}",
            create_client_msg,
            res
        );

        ctx.scope_port_to_module(msg_chan_init.port_id.clone(), module_id);

        // Figure out the ID of the client that was just created.
        let mut events = res.unwrap().events;
        let client_id_event = events.pop();
        assert!(
            client_id_event.is_some(),
            "There was no event generated for client creation!"
        );
        let client_id = match client_id_event.unwrap() {
            IbcEvent::CreateClient(create_client) => create_client.client_id().clone(),
            event => panic!("unexpected IBC event: {:?}", event),
        };

        let tests: Vec<Test> = vec![
            // Test some ICS2 client functionality.
            Test {
                name: "Client update successful".to_string(),
                msg: Ics26Envelope::Ics2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: client_id.clone(),
                    header: MockHeader::new(update_client_height)
                        .with_timestamp(Timestamp::now())
                        .into(),
                    signer: default_signer.clone(),
                })),
                want_pass: true,
            },
            Test {
                name: "Client update fails due to stale header".to_string(),
                msg: Ics26Envelope::Ics2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: client_id.clone(),
                    header: MockHeader::new(update_client_height).into(),
                    signer: default_signer.clone(),
                })),
                want_pass: false,
            },
            Test {
                name: "Connection open init succeeds".to_string(),
                msg: Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenInit(
                    msg_conn_init.with_client_id(client_id.clone()),
                )),
                want_pass: true,
            },
            Test {
                name: "Connection open try fails due to InvalidConsensusHeight (too high)"
                    .to_string(),
                msg: Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    incorrect_msg_conn_try,
                ))),
                want_pass: false,
            },
            Test {
                name: "Connection open try succeeds".to_string(),
                msg: Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenTry(Box::new(
                    correct_msg_conn_try.with_client_id(client_id.clone()),
                ))),
                want_pass: true,
            },
            Test {
                name: "Connection open ack succeeds".to_string(),
                msg: Ics26Envelope::Ics3Msg(ConnectionMsg::ConnectionOpenAck(Box::new(
                    msg_conn_ack,
                ))),
                want_pass: true,
            },
            // ICS04
            Test {
                name: "Channel open init succeeds".to_string(),
                msg: Ics26Envelope::Ics4ChannelMsg(ChannelMsg::ChannelOpenInit(msg_chan_init)),
                want_pass: true,
            },
            Test {
                name: "Channel open init fail due to missing connection".to_string(),
                msg: Ics26Envelope::Ics4ChannelMsg(ChannelMsg::ChannelOpenInit(
                    incorrect_msg_chan_init,
                )),
                want_pass: false,
            },
            Test {
                name: "Channel open try succeeds".to_string(),
                msg: Ics26Envelope::Ics4ChannelMsg(ChannelMsg::ChannelOpenTry(msg_chan_try)),
                want_pass: true,
            },
            Test {
                name: "Channel open ack succeeds".to_string(),
                msg: Ics26Envelope::Ics4ChannelMsg(ChannelMsg::ChannelOpenAck(msg_chan_ack)),
                want_pass: true,
            },
            //ICS20-04-packet
            Test {
                name: "Packet send".to_string(),
                msg: Ics26Envelope::Ics20Msg(msg_transfer),
                want_pass: true,
            },
            // The client update is required in this test, because the proof associated with
            // msg_recv_packet has the same height as the packet TO height (see get_dummy_raw_msg_recv_packet)
            Test {
                name: "Client update successful #2".to_string(),
                msg: Ics26Envelope::Ics2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: client_id.clone(),
                    header: MockHeader::new(update_client_height_after_send)
                        .with_timestamp(Timestamp::now())
                        .into(),
                    signer: default_signer.clone(),
                })),
                want_pass: true,
            },
            Test {
                name: "Receive packet".to_string(),
                msg: Ics26Envelope::Ics4PacketMsg(PacketMsg::RecvPacket(msg_recv_packet.clone())),
                want_pass: true,
            },
            Test {
                name: "Re-Receive packet".to_string(),
                msg: Ics26Envelope::Ics4PacketMsg(PacketMsg::RecvPacket(msg_recv_packet)),
                want_pass: true,
            },
            Test {
                name: "Packet send".to_string(),
                msg: Ics26Envelope::Ics20Msg(msg_transfer_two),
                want_pass: true,
            },
            Test {
                name: "Client update successful".to_string(),
                msg: Ics26Envelope::Ics2Msg(ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: client_id.clone(),
                    header: MockHeader::new(update_client_height_after_second_send).into(),
                    signer: default_signer.clone(),
                })),
                want_pass: true,
            },
            //ICS04-close channel
            Test {
                name: "Channel close init succeeds".to_string(),
                msg: Ics26Envelope::Ics4ChannelMsg(ChannelMsg::ChannelCloseInit(
                    msg_chan_close_init,
                )),
                want_pass: true,
            },
            Test {
                name: "Channel close confirm fails cause channel is already closed".to_string(),
                msg: Ics26Envelope::Ics4ChannelMsg(ChannelMsg::ChannelCloseConfirm(
                    msg_chan_close_confirm,
                )),
                want_pass: false,
            },
            //ICS04-to_on_close
            Test {
                name: "Timeout on close".to_string(),
                msg: Ics26Envelope::Ics4PacketMsg(PacketMsg::ToClosePacket(msg_to_on_close)),
                want_pass: true,
            },
            Test {
                name: "Client upgrade successful".to_string(),
                msg: Ics26Envelope::Ics2Msg(ClientMsg::UpgradeClient(MsgUpgradeAnyClient::new(
                    client_id.clone(),
                    AnyClientState::Mock(MockClientState::new(MockHeader::new(
                        upgrade_client_height,
                    ))),
                    AnyConsensusState::Mock(MockConsensusState::new(MockHeader::new(
                        upgrade_client_height,
                    ))),
                    get_dummy_merkle_proof(),
                    get_dummy_merkle_proof(),
                    default_signer.clone(),
                ))),
                want_pass: true,
            },
            Test {
                name: "Client upgrade un-successful".to_string(),
                msg: Ics26Envelope::Ics2Msg(ClientMsg::UpgradeClient(MsgUpgradeAnyClient::new(
                    client_id,
                    AnyClientState::Mock(MockClientState::new(MockHeader::new(
                        upgrade_client_height_second,
                    ))),
                    AnyConsensusState::Mock(MockConsensusState::new(MockHeader::new(
                        upgrade_client_height_second,
                    ))),
                    get_dummy_merkle_proof(),
                    get_dummy_merkle_proof(),
                    default_signer,
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
                "ICS26 routing dispatch test '{}' failed for message {:?}\nwith result: {:?}",
                test.name,
                test.msg,
                res
            );
        }
    }
}
