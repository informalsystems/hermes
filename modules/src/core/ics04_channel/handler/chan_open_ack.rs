//! Protocol logic specific to ICS4 messages of type `MsgChannelOpenAck`.
use crate::core::ics03_connection::connection::State as ConnectionState;
use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, State};
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::events::Attributes;
use crate::core::ics04_channel::handler::verify::verify_channel_proofs;
use crate::core::ics04_channel::handler::{ChannelIdState, ChannelResult};
use crate::core::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: &MsgChannelOpenAck,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    // Unwrap the old channel end and validate it against the message.
    let mut channel_end = ctx.channel_end(&(msg.port_id.clone(), msg.channel_id))?;

    // Validate that the channel end is in a state where it can be ack.
    if !channel_end.state_matches(&State::Init) && !channel_end.state_matches(&State::TryOpen) {
        return Err(Error::invalid_channel_state(
            msg.channel_id,
            channel_end.state,
        ));
    }

    // An OPEN IBC connection running on the local (host) chain should exist.

    if channel_end.connection_hops().len() != 1 {
        return Err(Error::invalid_connection_hops_length(
            1,
            channel_end.connection_hops().len(),
        ));
    }

    let conn = ctx.connection_end(&channel_end.connection_hops()[0])?;

    if !conn.state_matches(&ConnectionState::Open) {
        return Err(Error::connection_not_open(
            channel_end.connection_hops()[0].clone(),
        ));
    }

    // Proof verification in two steps:
    // 1. Setup: build the Channel as we expect to find it on the other party.

    let expected_counterparty = Counterparty::new(msg.port_id.clone(), Some(msg.channel_id));

    let counterparty = conn.counterparty();
    let ccid = counterparty.connection_id().ok_or_else(|| {
        Error::undefined_connection_counterparty(channel_end.connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::TryOpen,
        *channel_end.ordering(),
        expected_counterparty,
        expected_connection_hops,
        msg.counterparty_version.clone(),
    );

    // set the counterparty channel id to verify against it
    channel_end.set_counterparty_channel_id(msg.counterparty_channel_id);

    //2. Verify proofs
    verify_channel_proofs(
        ctx,
        msg.proofs.height(),
        &channel_end,
        &conn,
        &expected_channel_end,
        &msg.proofs,
    )?;

    output.log("success: channel open ack ");

    // Transition the channel end to the new state & pick a version.
    channel_end.set_state(State::Open);
    channel_end.set_version(msg.counterparty_version.clone());

    let result = ChannelResult {
        port_id: msg.port_id.clone(),
        channel_id: msg.channel_id,
        channel_id_state: ChannelIdState::Reused,
        channel_end,
    };

    let event_attributes = Attributes {
        channel_id: Some(msg.channel_id),
        height: ctx.host_height(),
        ..Default::default()
    };
    output.emit(IbcEvent::OpenAckChannel(
        event_attributes
            .try_into()
            .map_err(|_| Error::missing_channel_id())?,
    ));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use test_log::test;

    use crate::core::ics03_connection::connection::ConnectionEnd;
    use crate::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::core::ics03_connection::connection::State as ConnectionState;
    use crate::core::ics03_connection::msgs::conn_open_init::test_util::get_dummy_raw_msg_conn_open_init;
    use crate::core::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::core::ics03_connection::msgs::conn_open_try::test_util::get_dummy_raw_msg_conn_open_try;
    use crate::core::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
    use crate::core::ics03_connection::version::get_compatible_versions;
    use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, State};
    use crate::core::ics04_channel::context::ChannelReader;
    use crate::core::ics04_channel::handler::channel_dispatch;
    use crate::core::ics04_channel::msgs::chan_open_ack::test_util::get_dummy_raw_msg_chan_open_ack;
    use crate::core::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
    use crate::core::ics04_channel::msgs::chan_open_try::test_util::get_dummy_raw_msg_chan_open_try;
    use crate::core::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
    use crate::core::ics04_channel::msgs::ChannelMsg;
    use crate::core::ics24_host::identifier::ConnectionId;
    use crate::events::IbcEvent;
    use crate::mock::context::MockContext;
    use crate::prelude::*;
    use crate::Height;

    // TODO: The tests here are very fragile and complex.
    //  Should be adapted to use the same structure as `handler::chan_open_try::tests`.
    #[test]
    fn chan_open_ack_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ChannelMsg,
            want_pass: bool,
        }
        let proof_height = 10;
        let client_consensus_state_height = 10;
        let host_chain_height = Height::new(0, 35);

        let context = MockContext::default();

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_raw_msg_conn_open_init()).unwrap();

        let conn_end = ConnectionEnd::new(
            ConnectionState::Open,
            msg_conn_init.client_id.clone(),
            ConnectionCounterparty::new(
                msg_conn_init.counterparty.client_id().clone(),
                Some(ConnectionId::from_str("defaultConnection-1").unwrap()),
                msg_conn_init.counterparty.prefix().clone(),
            ),
            get_compatible_versions(),
            msg_conn_init.delay_period,
        );

        let ccid = <ConnectionId as FromStr>::from_str("defaultConnection-0");
        let cid = match ccid {
            Ok(v) => v,
            Err(_e) => ConnectionId::default(),
        };

        let mut connection_vec0 = Vec::new();
        connection_vec0.insert(
            0,
            match <ConnectionId as FromStr>::from_str("defaultConnection-0") {
                Ok(a) => a,
                _ => unreachable!(),
            },
        );

        let msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
            client_consensus_state_height,
            host_chain_height.revision_height,
        ))
        .unwrap();

        let msg_chan_ack =
            MsgChannelOpenAck::try_from(get_dummy_raw_msg_chan_open_ack(proof_height)).unwrap();

        let msg_chan_try =
            MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height)).unwrap();

        let chan_end = ChannelEnd::new(
            State::Init,
            *msg_chan_try.channel.ordering(),
            Counterparty::new(msg_chan_ack.port_id.clone(), Some(msg_chan_ack.channel_id)),
            connection_vec0.clone(),
            msg_chan_try.channel.version().clone(),
        );

        let failed_chan_end = ChannelEnd::new(
            State::Open,
            *msg_chan_try.channel.ordering(),
            Counterparty::new(msg_chan_ack.port_id.clone(), Some(msg_chan_ack.channel_id)),
            connection_vec0,
            msg_chan_try.channel.version().clone(),
        );

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no channel exists in the context".to_string(),
                ctx: context.clone(),
                msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the channel is in the wrong state".to_string(),
                ctx: context
                    .clone()
                    .with_client(
                        &msg_conn_try.client_id,
                        Height::new(0, client_consensus_state_height),
                    )
                    .with_channel(
                        msg_chan_ack.port_id.clone(),
                        msg_chan_ack.channel_id,
                        failed_chan_end,
                    ),
                msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because a connection does exist".to_string(),
                ctx: context
                    .clone()
                    .with_client(
                        &msg_conn_try.client_id,
                        Height::new(0, client_consensus_state_height),
                    )
                    .with_channel(
                        msg_chan_ack.port_id.clone(),
                        msg_chan_ack.channel_id,
                        chan_end.clone(),
                    ),
                msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails due to missing client state ".to_string(),
                ctx: context
                    .clone()
                    .with_connection(cid.clone(), conn_end.clone())
                    .with_channel(
                        msg_chan_ack.port_id.clone(),
                        msg_chan_ack.channel_id,
                        chan_end.clone(),
                    ),
                msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context //  .clone()
                    .with_client(
                        &msg_conn_try.client_id,
                        Height::new(0, client_consensus_state_height),
                    )
                    .with_connection(cid, conn_end)
                    .with_channel(
                        msg_chan_ack.port_id.clone(),
                        msg_chan_ack.channel_id,
                        chan_end,
                    ),
                msg: ChannelMsg::ChannelOpenAck(msg_chan_ack),
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = channel_dispatch(&test.ctx, &test.msg);
            // Additionally check the events and the output objects in the result.
            match res {
                Ok((proto_output, res)) => {
                    assert!(
                            test.want_pass,
                            "chan_open_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                            test.name,
                            test.msg,
                            test.ctx.clone()
                        );

                    let proto_output = proto_output.with_result(());
                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have init state.
                    //assert_eq!(res.channel_id, msg_chan_init.channel_id().clone());
                    assert_eq!(res.channel_end.state().clone(), State::Open);

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::OpenAckChannel(_)));
                        assert_eq!(e.height(), test.ctx.host_height());
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "chan_open_ack: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
