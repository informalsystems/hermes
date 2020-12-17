//! Protocol logic specific to ICS3 messages of type `MsgChannelOpenInit`.

use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::channel::{ChannelEnd,State};
use crate::ics04_channel::error::{Error,Kind};
use crate::ics04_channel::handler::ChannelEvent::ChanOpenInit;
use crate::ics04_channel::handler::ChannelResult;
use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: MsgChannelOpenInit,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();




    let pc_id = (msg.port_id().clone(),msg.channel_id().clone());

    if ctx.channel_end(&pc_id).is_some() {
        return Err(Kind::ChannelExistsAlready(msg.channel_id().clone()).into());
    } 
    //TODO what about the port capabilities  ?

    

    if msg.channel().connection_hops().len() != 1 { 
        return Err(Kind::InvalidConnectionHopsLength.into()); 
        }

    // An IBC connection running on the local (host) chain should exist.
    if ctx.connection_state(&msg.channel().connection_hops()[0]).is_none() {
        return Err(Kind::MissingConnection(msg.channel().connection_hops()[0].clone()).into());
    }

    //TODO Check Version non Empty but not necessary coherent  
     if msg.channel().version()== "" { 
        return Err(Kind::InvalidVersion.into()); 
        }


    let new_channel_end = ChannelEnd::new(
        State::Init,
        *msg.channel().ordering(), 
        msg.channel().counterparty(),
        msg.channel().connection_hops(),
        ctx.get_compatible_versions()[0].clone(),
    );
    

    output.log("success: no channel found");

    let result = ChannelResult {
        port_id: msg.port_id().clone(),
        channel_id: msg.channel_id().clone(),
        channel_end: new_channel_end,
    };

    output.emit(ChanOpenInit(result.clone()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use crate::handler::EventType;

    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::connection::ConnectionEnd;


    use crate::ics04_channel::channel::{ChannelEnd, State};

    use crate::ics04_channel::handler::{dispatch, ChannelResult};
    use crate::ics04_channel::msgs::chan_open_init::test_util::get_dummy_raw_msg_chan_open_init;

    use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use crate::ics04_channel::msgs::ChannelMsg;
    use crate::mock::context::MockContext;

     #[test]
    fn chan_open_init_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ChannelMsg,
            want_pass: bool,
        }

         let msg_chan_init =
             MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init()).unwrap();

             
         let context = MockContext::default();

        let init_chan_end = &ChannelEnd::new(
            State::Init,
            *msg_chan_init.channel().ordering(),
            msg_chan_init.channel().counterparty(),
            msg_chan_init.channel().connection_hops(),
            "ics20".to_string(),
        );

        let msg_conn_init =
        MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();

        let init_conn_end = &ConnectionEnd::test_channel_new(
            msg_conn_init.client_id().clone(),
            msg_conn_init.counterparty().clone(),
        ).unwrap();
    

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because the channel exists in the store already"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_channel(msg_chan_init.port_id().clone(),msg_chan_init.channel_id().clone(), init_chan_end.clone()),
                msg: ChannelMsg::ChannelOpenInit(msg_chan_init.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because no connection exists in the context".to_string(),
                ctx: context.clone(),
                msg: ChannelMsg::ChannelOpenInit(msg_chan_init.clone()),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context.with_connection(MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap().connection_id().clone(), init_conn_end.clone()),
                msg: ChannelMsg::ChannelOpenInit(msg_chan_init.clone()),
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
                    assert_eq!(res.channel_id, msg_chan_init.channel_id().clone());
                    assert_eq!(res.channel_end.state().clone(), State::Init);

                    for e in proto_output.events.iter() {
                        assert_eq!(e.tpe, EventType::Custom("channel_open_init".to_string()));
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
