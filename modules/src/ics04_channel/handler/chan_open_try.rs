//! Protocol logic specific to ICS4 messages of type `MsgChannelOpenTry`.

use Kind::ConnectionNotOpen;

use crate::events::IBCEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::State as ConnectionState;
use crate::ics04_channel::channel::{ChannelEnd, Counterparty, State};
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::events::Attributes;
use crate::ics04_channel::handler::ChannelResult;
use crate::ics04_channel::handler::verify::verify_proofs;
use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use crate::ics24_host::identifier::ChannelId;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: MsgChannelOpenTry,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    // Unwrap the old channel end (if any) and validate it against the message.
    let (mut new_channel_end, channel_id) = match msg.previous_channel_id() {
        Some(prev_id) => {
            let old_channel_end = ctx
                .channel_end(&(msg.port_id().clone(), prev_id.clone()))
                .ok_or_else(|| Kind::ChannelNotFound.context(prev_id.to_string()))?;

            // Validate that existing channel end matches with the one we're trying to establish.
            if old_channel_end.state_matches(&State::Init)
                && old_channel_end.order_matches(&msg.channel.ordering())
                && old_channel_end.connection_hops_matches(&msg.channel.connection_hops())
                && old_channel_end.counterparty_matches(msg.channel.counterparty())
                && old_channel_end.version_matches(&msg.channel.version())
            {
                // A ChannelEnd already exists and all validation passed.
                Ok((old_channel_end, prev_id.clone()))
            } else {
                // TODO(ADI) Fix this: no need for context!
                // A ConnectionEnd already exists and validation failed.
                Err(Into::<Error>::into(
                    Kind::ChannelMismatch(prev_id.clone()).context(
                        old_channel_end
                            .counterparty()
                            .channel_id()
                            .clone()
                            .unwrap()
                            .to_string(),
                    ),
                ))
            }
        }
        // No previous channel id was supplied. Create a new channel end & an identifier.
        None => {
            let channel_end = ChannelEnd::new(
                State::Init,
                *msg.channel.ordering(),
                msg.channel.counterparty().clone(),
                msg.channel.connection_hops().clone(),
                msg.counterparty_version().clone(),
            );

            // Channel identifier construction.
            let id_counter = ctx.channel_counter();
            let chan_id = ChannelId::new(id_counter)
                .map_err(|e| Kind::ChannelIdentifierConstructor(id_counter, e.kind().clone()))?;

            output.log(format!(
                "success: generated new channel identifier: {}",
                chan_id
            ));

            Ok((channel_end, chan_id))
        }
    }?;

    // An IBC connection running on the local (host) chain should exist.
    if msg.channel.connection_hops().len() != 1 {
        return Err(
            Kind::InvalidConnectionHopsLength(1, msg.channel.connection_hops().len()).into(),
        );
    }

    let connection_end_opt = ctx.connection_end(&msg.channel().connection_hops()[0]);

    let conn = connection_end_opt
        .ok_or_else(|| Kind::MissingConnection(msg.channel().connection_hops()[0].clone()))?;

    if !conn.state_matches(&ConnectionState::Open) {
        return Err(ConnectionNotOpen(msg.channel.connection_hops()[0].clone()).into());
    }

    let get_versions = conn.versions();
    let version = match get_versions.as_slice() {
        [version] => version,
        _ => return Err(Kind::InvalidVersionLengthConnection.into()),
    };

    let channel_feature = msg.channel().ordering().as_string().to_string();
    if !version.is_supported_feature(channel_feature) {
        return Err(Kind::ChannelFeatureNotSuportedByConnection.into());
    }

    // Channel capabilities
    let channel_cap = ctx.authenticated_capability(&msg.port_id().clone())?;

    if msg.channel().version().is_empty() {
        return Err(Kind::InvalidVersion.into());
    }

    // Proof verification in two steps:
    // 1. Setup: build the Channel as we expect to find it on the other party.

    let expected_counterparty = Counterparty::new(msg.port_id().clone(), None);

    let counterparty = conn.counterparty();
    let ccid = counterparty.connection_id().ok_or_else(|| {
        Kind::UndefinedConnectionCounterparty(msg.channel().connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::Init,
        *msg.channel.ordering(),
        expected_counterparty,
        expected_connection_hops,
        msg.counterparty_version().clone(),
    );

    verify_proofs(
        ctx,
        &new_channel_end,
        &conn,
        &expected_channel_end,
        &msg.proofs(),
    )
    .map_err(|e| Kind::FailedChanneOpenTryVerification.context(e))?;

    output.log("success: channel open try ");

    // Transition the channel end to the new state & pick a version.
    new_channel_end.set_state(State::TryOpen);

    let result = ChannelResult {
        port_id: msg.port_id().clone(),
        channel_cap,
        previous_channel_id: msg.previous_channel_id.clone(),
        channel_id: channel_id.clone(),
        channel_end: new_channel_end,
    };

    let event_attributes = Attributes {
        channel_id: Some(channel_id),
        ..Default::default()
    };
    output.emit(IBCEvent::OpenTryChannel(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
#[allow(clippy::all)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::events::IBCEvent;
    use crate::Height;
    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::ics03_connection::connection::State as ConnectionState;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
    use crate::ics03_connection::msgs::conn_open_try::test_util::get_dummy_msg_conn_open_try;
    use crate::ics03_connection::msgs::test_util::get_dummy_counterparty;
    use crate::ics03_connection::version::get_compatible_versions;
    use crate::ics04_channel::channel::{ChannelEnd, State};
    use crate::ics04_channel::handler::{ChannelResult, dispatch};
    use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
    use crate::ics04_channel::msgs::chan_open_try::test_util::get_dummy_raw_msg_chan_open_try;
    use crate::ics04_channel::msgs::chan_open_try::test_util::get_dummy_raw_msg_chan_open_try_with_counterparty;
    use crate::ics04_channel::msgs::ChannelMsg;
    use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
    use crate::mock::context::MockContext;

    #[test]
    fn chan_open_try_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ChannelMsg,
            want_pass: bool,
        }

        // Some general-purpose variable to parametrize the messages and the context.
        let proof_height = 10;
        let client_consensus_state_height = 10;
        let host_chain_height = Height::new(1, 35);
        let conn_id = ConnectionId::default();
        let connection_vec = vec![conn_id.clone()];

        // The context. We'll reuse this same one across all tests.
        let context = MockContext::default();

        // This is the connection underlying the channel we're trying to open.
        let conn_end = ConnectionEnd::new(
            ConnectionState::Open,
            ClientId::default(),
            ConnectionCounterparty::try_from(get_dummy_counterparty()).unwrap(),
            get_compatible_versions(),
            msg_conn_init.delay_period,
        );

        // This is used to add a channel to the context.
        let cchan_id2 = <ChannelId as FromStr>::from_str(&"channel24".to_string());

        let chan_id = ChannelId::new(24).unwrap();

        //msg_chan_try2 is used to test against an exiting channel entry.
        let cchan_id = <ChannelId as FromStr>::from_str(&"channel24".to_string());

        let mut msg_chan_try2 =
            MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height)).unwrap();

        msg_chan_try2.previous_channel_id = match cchan_id {
            Ok(v) => Some(v),
            Err(_e) => None,
        };

        let init_chan_end = ChannelEnd::new(
            State::Init,
            *msg_chan_try2.channel.ordering(),
            msg_chan_try2.channel.counterparty().clone(),
            connection_vec.clone(),
            msg_chan_try2.channel.version(),
        );

        let init_chan_end2 = ChannelEnd::new(
            State::Init,
            *msg_chan_try2.channel.ordering(),
            msg_chan_try2.channel.counterparty().clone(),
            //msg_chan_try.channel.connection_hops().clone(),
            connection_vec,
            msg_chan_try2.counterparty_version().clone(),
        );

        //Used for Test "Processing connection does not match when a channel exists "
        let mut connection_vec3 = Vec::new();
        connection_vec3.insert(0, ConnectionId::default());

        let init_chan_end3 = ChannelEnd::new(
            State::Init,
            *msg_chan_try2.channel.ordering(),
            msg_chan_try2.channel.counterparty().clone(),
            connection_vec3,
            msg_chan_try2.channel().version(),
        );

        let msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_msg_conn_open_try(
            client_consensus_state_height,
            host_chain_height.revision_height,
        ))
        .unwrap();

        let msg_chan_try = MsgChannelOpenTry::try_from(
            get_dummy_raw_msg_chan_open_try_with_counterparty(proof_height),
        )
        .unwrap();

        let ccounterparty_chan_id = <ChannelId as FromStr>::from_str(&"channel25".to_string());
        let counterparty_chan_id = match ccounterparty_chan_id {
            Ok(v) => v,
            Err(_e) => ChannelId::default(),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no connection exists in the context".to_string(),
                ctx: context.clone(),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because the port does not have a capability associated"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_connection(conn_id.clone(), conn_end.clone()),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing version does not match when a channel exists ".to_string(),
                ctx: context
                    .clone()
                    .with_connection(conn_id.clone(), conn_end.clone())
                    .with_port_capability(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                    )
                    .with_channel(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                        chan_id.clone(),
                        init_chan_end2,
                    ),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try2.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing connection does not match when a channel exists ".to_string(),
                ctx: context
                    .clone()
                    .with_connection(conn_id.clone(), conn_end.clone())
                    .with_port_capability(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                    )
                    .with_channel(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                        chan_id.clone(),
                        init_chan_end3,
                    ),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try2.clone()),
                want_pass: false,
            },
            Test {
                name: " Channel Open Try fails due to missing client state ".to_string(),
                ctx: context
                    .clone()
                    .with_connection(conn_id.clone(), conn_end.clone())
                    .with_port_capability(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                    )
                    .with_channel(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                        chan_id.clone(),
                        init_chan_end.clone(),
                    ),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try2.clone()),
                want_pass: false,
            },
            Test {
                name: "Good parameters: Channel Open Init found ".to_string(),
                ctx: context
                    .clone()
                    .with_client(
                        msg_conn_try.client_id(),
                        Height::new(1, client_consensus_state_height),
                    )
                    .with_connection(conn_id.clone(), conn_end.clone())
                    .with_port_capability(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                    )
                    .with_channel(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                        chan_id,
                        init_chan_end.clone(),
                    ),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try2),
                want_pass: true,
            },
            Test {
                name: "Good parameters: No channel Open Init found".to_string(),
                ctx: context
                    .with_client(
                        msg_conn_try.client_id(),
                        Height::new(1, client_consensus_state_height),
                    )
                    .with_connection(conn_id, conn_end)
                    .with_port_capability(
                        MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone(),
                    )
                    .with_channel(
                        PortId::from_str("port12").unwrap(),
                        counterparty_chan_id,
                        init_chan_end,
                    ),
                msg: ChannelMsg::ChannelOpenTry(msg_chan_try),
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
                        "chan_open_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have init state.
                    let res: ChannelResult = proto_output.result;
                    //assert_eq!(res.channel_id, msg_chan_init.channel_id().clone());
                    assert_eq!(res.channel_end.state().clone(), State::TryOpen);

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IBCEvent::OpenTryChannel(_)));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "chan_open_try: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
