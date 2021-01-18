//! Protocol logic specific to ICS4 messages of type `MsgChannelOpenTry`.

use Kind::ConnectionNotOpen;

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::State as ConnectionState;
use crate::ics04_channel::channel::{ChannelEnd, State};
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::handler::verify::verify_proofs;
use crate::ics04_channel::handler::ChannelEvent::ChanOpenTry;
use crate::ics04_channel::handler::ChannelResult;
use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
//use crate::ics24_host::identifier::ChannelId;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: MsgChannelOpenTry,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    let channel_id;

    // Unwrap the old channel end (if any) and validate it against the message.

    let mut new_channel_end = match msg.previous_channel_id() {
        Some(prev_id) => {
            let old_channel_end = ctx
                .channel_end(&(msg.port_id().clone(), prev_id.clone()))
                .ok_or_else(|| Kind::ChannelNotFound.context(prev_id.to_string()))?;

            channel_id = Some(prev_id.clone());
            // Validate that existing channel end matches with the one we're trying to establish.

            if old_channel_end.state_matches(&State::Init)
                && old_channel_end.order_matches(&msg.channel.ordering())
                && old_channel_end.connection_hops_matches(&msg.channel.connection_hops())
                && old_channel_end.counterparty_matches(msg.channel.counterparty())
               // && old_channel_end.version_matches(&msg.counterparty_version().clone())
               && old_channel_end.version_matches(&msg.channel.version())
            {
                // A ChannelEnd already exists and all validation passed.
                Ok(old_channel_end)
            } else {
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
        // No channel id is supplied to  create a new channel end. Note: the id is assigned
        // by the ChannelKeeper.
        None => {
            channel_id = None;

            Ok(ChannelEnd::new(
                State::Init,
                *msg.channel.ordering(),
                msg.channel.counterparty().clone(),
                msg.channel.connection_hops().clone(),
                msg.counterparty_version().clone(),
            ))
        }
    }?;

    if msg.channel.connection_hops().len() != 1 {
        return Err(Kind::InvalidConnectionHopsLength.into());
    }

    let connection_end = ctx.connection_state(&msg.channel().connection_hops()[0]);

    let conn = connection_end
        .ok_or_else(|| Kind::MissingConnection(msg.channel().connection_hops()[0].clone()))?;

    //assert!(conn.state_matches(&ConnectionState::Open));

    if !conn.state_matches(&ConnectionState::Open)
        {
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

    // An IBC connection running on the local (host) chain should exist.
    


    //Channel capabilities
    let cap = ctx.port_capability(&msg.port_id().clone());
    let cap_key;

    match cap {
        Some(key) => {
            if !ctx.capability_authentification(&msg.port_id().clone(), &key) {
                return Err(Kind::InvalidPortCapability.into());
            } else {
                cap_key = key;
            }
        }
        None => return Err(Kind::NoPortCapability.into()),
    }

    

    // // TODO: Check that `version` is non empty but not necessary coherent
    // if msg.channel().version().is_empty() {
    //     return Err(Kind::InvalidVersion.into());
    // }

    // Proof verification in two steps:
    // 1. Setup: build the Channel as we expect to find it on the other party.

    let expected_channel_end = ChannelEnd::new(
        State::Init,
        *msg.channel.ordering(),
        msg.channel.counterparty().clone(),
        msg.channel.connection_hops().clone(),
        msg.counterparty_version().clone(),
    );

    if !verify_proofs(ctx, &new_channel_end, &expected_channel_end) {
        return Err(Kind::MissingChannel.into());
    }
    output.log("success: channel open try ");

    // Transition the connection end to the new state & pick a version.
    new_channel_end.set_state(State::TryOpen);

    let result = ChannelResult {
        port_id: msg.port_id().clone(),
        channel_id,
        channel_cap: cap_key,
        channel_end: new_channel_end,
    };

    output.emit(ChanOpenTry(result.clone()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::handler::EventType;

    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::connection::State as ConnectionState;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::version::get_compatible_versions;

    use crate::ics04_channel::channel::{ChannelEnd, State};
    use crate::ics04_channel::handler::{dispatch, ChannelResult};
    use crate::ics04_channel::msgs::chan_open_try::test_util::get_dummy_raw_msg_chan_open_try;
    use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
    //use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use crate::ics04_channel::msgs::ChannelMsg;

    use crate::ics24_host::identifier::ChannelId;
    use crate::ics24_host::identifier::ConnectionId;
    use crate::mock::context::MockContext;
    // use crate::Height;

    #[test]
    fn chan_open_try_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ChannelMsg,
            want_pass: bool,
        }
        let proof_height = 10;
        //let client_consensus_state_height = 10;

        let msg_chan_try =
            MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height)).unwrap();

        //chan_id is used to add a channel to the context
        let cchan_id2 = <ChannelId as FromStr>::from_str(&"channel24".to_string());

        let chan_id = match cchan_id2 {
            Ok(v) => v,
            Err(_e) => ChannelId::default(),
        };

        //msg_chan_try2 is used to test against an exiting channel entry.
        let cchan_id = <ChannelId as FromStr>::from_str(&"channel24".to_string());
        let mut msg_chan_try2 =
            MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height)).unwrap();

        msg_chan_try2.previous_channel_id = match cchan_id {
            Ok(v) => Some(v),
            Err(_e) => None,
        };

        let proof_height = 10;
        // let default_raw_msg = get_dummy_raw_msg_chan_open_try(proof_height);

        let context = MockContext::default();

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();

        //let conn_state =  <ConnectionState as TryFrom<i32>>::try_from(1).unwrap(); 
        let init_conn_end = ConnectionEnd::new(
           // conn_state.clone(),
           ConnectionState::Open,
           //crate::ics03_connection::connection::State::Init,
            msg_conn_init.client_id().clone(),
            msg_conn_init.counterparty().clone(),
            get_compatible_versions(),
            msg_conn_init.delay_period,
        );

        //assert!(init_conn_end.state_matches(&ConnectionState::Init));
        // init_conn_end.set_state(ConnectionState::Init);

        let ccid = <ConnectionId as FromStr>::from_str("defaultConnection-0");
        let cid = match ccid {
            Ok(v) => v,
            Err(_e) => ConnectionId::default(),
        };

        let mut connection_vec = Vec::new();
        // connection_vec.insert(0, ConnectionId::default());
        connection_vec.insert(
            0,
            match <ConnectionId as FromStr>::from_str("defaultConnection-0") {
                Ok(a) => a,
                _ => unreachable!(),
            },
        );

        let mut connection_vec3 = Vec::new();
        connection_vec3.insert(0, ConnectionId::default());

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
            connection_vec.clone(),
            msg_chan_try2.counterparty_version().clone(),
        );

        let init_chan_end3 = ChannelEnd::new(
            State::Init,
            *msg_chan_try2.channel.ordering(),
            msg_chan_try2.channel.counterparty().clone(),
            //msg_chan_try.channel.connection_hops().clone(),
            connection_vec3,
            msg_chan_try2.channel().version().clone(),
        );

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no connection exists in the context".to_string(),
                ctx: context.clone(),
                msg: ChannelMsg::ChannelOpenTry(Box::new(msg_chan_try.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing fails because port does not have a capability associated"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_connection(cid.clone(), init_conn_end.clone()),
                msg: ChannelMsg::ChannelOpenTry(Box::new(msg_chan_try.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing version does not match when a channel exists ".to_string(),
                ctx: context.clone()
                .with_connection(cid.clone(),init_conn_end.clone())
                .with_port_capability(MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                    .unwrap()
                    .port_id()
                    .clone())
                .with_channel_init(
                    MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                        .unwrap()
                        .port_id()
                        .clone(),
                    chan_id.clone(),
                    init_chan_end2,
                ),
                msg: ChannelMsg::ChannelOpenTry(Box::new(msg_chan_try2.clone())),
                want_pass: false,
            },
            Test {
                name: "Processing connection does not match when a channel exists ".to_string(),
                ctx: context.clone()
                .with_connection(cid.clone(),init_conn_end.clone())
                .with_port_capability(
                    MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                    .unwrap()
                    .port_id()
                     .clone())
                .with_channel_init(
                    MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                        .unwrap()
                        .port_id()
                        .clone(),
                    chan_id.clone(),
                    init_chan_end3,
                ),
                msg: ChannelMsg::ChannelOpenTry(Box::new(msg_chan_try2.clone())),
                want_pass: false,
            },
            Test {
                name: "Good parameters: Channel Open Init found ".to_string(),
                ctx: context.clone()
                    .with_connection(cid.clone(),init_conn_end.clone())
                    .with_port_capability(MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                            .unwrap()
                            .port_id()
                            .clone())
                    .with_channel_init(MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                        .unwrap()
                        .port_id()
                        .clone(),
                    chan_id,
                    init_chan_end,
                ),
                msg: ChannelMsg::ChannelOpenTry(Box::new(msg_chan_try2)),
                want_pass: true,
            },
            Test {
                name: "Good parameters: No channel Open Init found".to_string(),
                ctx: context.with_connection(cid,
                    init_conn_end).with_port_capability(
                    MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height))
                        .unwrap()
                        .port_id()
                        .clone(),
                ),
                msg: ChannelMsg::ChannelOpenTry(Box::new(msg_chan_try)),
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
                    let res: ChannelResult = proto_output.result;
                    //assert_eq!(res.channel_id, msg_chan_init.channel_id().clone());
                    assert_eq!(res.channel_end.state().clone(), State::TryOpen);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("channel_open_try".to_string()));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "chan_open_init: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
